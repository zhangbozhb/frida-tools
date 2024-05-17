interface MethodTypeSignature {
    argInfo: { [key: number]: boolean };
    retType: boolean;
    sel?: string;
}

interface MethodSignature extends MethodTypeSignature {
    name: string;
    className: string;
    fullName: string;
}

const runtime = (function () {
    // 运行时 api
    const _api_ext: { [name: string]: any } = {};
    const runtime_api_defs: { [key: string]: any } = {
        method_getNumberOfArguments: ["uint", ["pointer"]],
        method_copyArgumentType: ["pointer", ["pointer", "int"]],
        method_copyReturnType: ["pointer", ["pointer"]],
    };
    const runtime_api = new Proxy(ObjC.api, {
        get(target, p, receiver) {
            const ps = p as string;
            let tp = target[ps];
            if (tp) {
                return tp;
            }
            let defs = runtime_api_defs[ps];
            if (defs) {
                const api_address = Module.getExportByName(
                    "libobjc.A.dylib",
                    ps
                );
                const defaultInvocationOptions = {
                    exceptions: "propagate" as ExceptionsBehavior,
                };
                const funcPtr = new NativeFunction(
                    api_address,
                    defs[0],
                    defs[1],
                    defaultInvocationOptions
                );
                _api_ext[ps] = funcPtr;
                return funcPtr;
            }
        },
    });

    // 是否是 OC类型
    const isObjcType = (typeStr: string) => {
        // https://developer.apple.com/library/archive/documentation/Cocoa/Conceptual/ObjCRuntimeGuide/Articles/ocrtTypeEncodings.html#//apple_ref/doc/uid/TP40008048-CH100-SW1
        https: while (typeStr && /^[rnNoORV]/.test(typeStr)) {
            typeStr = typeStr.substring(1);
        }
        return /^[@#]$/.test(typeStr);
    };

    return {
        api: runtime_api,
        // 获取函数信息
        methodFromAPI(api: ApiResolverMatch) {
            const { name } = api;
            const [className, mName] = name
                .substring(2, name.length - 1)
                .split(" ", 2);
            const methodName = `${name[0]} ${mName}`;
            const cls = ObjC.classes[className];
            const method = cls[methodName] as ObjC.ObjectMethod;
            return { method, className, methodName };
        },
        isObjcType,
        // 获取函数 参数返回值签名
        methdTypeSignatureOf(methodHandle: NativePointer) {
            const numberOfArg =
                runtime_api.method_getNumberOfArguments(methodHandle);
            const argInfo: { [key: number]: boolean } = {};
            for (let argIndex = 2; argIndex < numberOfArg; argIndex++) {
                const argTypePrt = runtime_api.method_copyArgumentType(
                    methodHandle,
                    argIndex
                );
                const argType = argTypePrt.readUtf8String();
                runtime_api.free(argTypePrt);
                if (isObjcType(argType)) {
                    argInfo[argIndex - 2] = true;
                }
            }
            const retTypePtr = runtime_api.method_copyReturnType(methodHandle);
            const retType = isObjcType(retTypePtr.readUtf8String());
            const signature: MethodTypeSignature = {
                argInfo: argInfo,
                retType: retType,
            };
            return signature;
        },
    };
})();

class Agent {
    private handlers = new Map<TraceTargetId, TraceHandler>();
    private stackDepth = new Map<ThreadId, number>();
    private traceState: TraceState = {};
    private nextId = 1;
    private started = Date.now();

    private pendingEvents: TraceEvent[] = [];
    private flushTimer: any = null;

    private cachedModuleResolver: ApiResolver | null = null;
    private cachedObjcResolver: ApiResolver | null = null;
    private cachedSwiftResolver: ApiResolver | null = null;

    init(
        stage: Stage,
        parameters: TraceParameters,
        initScripts: InitScript[],
        spec: TraceSpec
    ) {
        const g = global as any as TraceScriptGlobals;
        g.stage = stage;
        g.parameters = parameters;
        g.state = this.traceState;

        for (const script of initScripts) {
            try {
                (1, eval)(script.source);
            } catch (e: any) {
                throw new Error(
                    `Unable to load ${script.filename}: ${e.stack}`
                );
            }
        }

        this.start(spec).catch((e) => {
            send({
                type: "agent:error",
                message: e.message,
            });
        });
    }

    dispose() {
        this.flush();
    }

    update(id: TraceTargetId, name: string, script: HandlerScript) {
        const handler = this.handlers.get(id);
        if (handler === undefined) {
            throw new Error("Invalid target ID");
        }

        const newHandler = this.parseHandler(name, script);
        handler[0] = newHandler[0];
        handler[1] = newHandler[1];
    }

    private async start(spec: TraceSpec) {
        const plan: TracePlan = {
            native: new Map<NativeId, NativeTarget>(),
            java: [],
        };

        const javaEntries: [TraceSpecOperation, TraceSpecPattern][] = [];
        for (const [operation, scope, pattern] of spec) {
            switch (scope) {
                case "module":
                    if (operation === "include") {
                        this.includeModule(pattern, plan);
                    } else {
                        this.excludeModule(pattern, plan);
                    }
                    break;
                case "function":
                    if (operation === "include") {
                        this.includeFunction(pattern, plan);
                    } else {
                        this.excludeFunction(pattern, plan);
                    }
                    break;
                case "relative-function":
                    if (operation === "include") {
                        this.includeRelativeFunction(pattern, plan);
                    }
                    break;
                case "imports":
                    if (operation === "include") {
                        this.includeImports(pattern, plan);
                    }
                    break;
                case "objc-method":
                    if (operation === "include") {
                        this.includeObjCMethod(pattern, plan);
                    } else if (operation === "exclude") {
                        this.excludeObjCMethod(pattern, plan);
                    } else if (operation === "filter") {
                        this.filterObjCMethod(pattern, plan);
                    }
                    break;
                case "objc-property":
                    if (operation === "exclude") {
                        this.excludeObjCProperty(pattern, plan);
                    }
                    break;
                case "swift-func":
                    if (operation === "include") {
                        this.includeSwiftFunc(pattern, plan);
                    } else {
                        this.excludeSwiftFunc(pattern, plan);
                    }
                    break;
                case "java-method":
                    javaEntries.push([operation, pattern]);
                    break;
                case "debug-symbol":
                    if (operation === "include") {
                        this.includeDebugSymbol(pattern, plan);
                    }
                    break;
            }
        }

        let javaStartRequest: Promise<void>;
        let javaStartDeferred = true;
        if (javaEntries.length > 0) {
            if (!Java.available) {
                throw new Error("Java runtime is not available");
            }

            javaStartRequest = new Promise((resolve, reject) => {
                Java.perform(() => {
                    javaStartDeferred = false;

                    for (const [operation, pattern] of javaEntries) {
                        if (operation === "include") {
                            this.includeJavaMethod(pattern, plan);
                        } else {
                            this.excludeJavaMethod(pattern, plan);
                        }
                    }

                    this.traceJavaTargets(plan.java)
                        .then(resolve)
                        .catch(reject);
                });
            });
        } else {
            javaStartRequest = Promise.resolve();
        }

        await this.traceNativeTargets(plan.native);

        if (!javaStartDeferred) {
            await javaStartRequest;
        }

        send({
            type: "agent:initialized",
        });

        javaStartRequest.then(() => {
            send({
                type: "agent:started",
                count: this.handlers.size,
            });
        });
    }

    private async traceNativeTargets(targets: NativeTargets) {
        const cGroups = new Map<string, NativeItem[]>();
        const objcGroups = new Map<string, NativeItem[]>();
        const swiftGroups = new Map<string, NativeItem[]>();

        for (const [id, [type, scope, name]] of targets.entries()) {
            let entries: Map<string, NativeItem[]>;
            switch (type) {
                case "c":
                    entries = cGroups;
                    break;
                case "objc":
                    entries = objcGroups;
                    break;
                case "swift":
                    entries = swiftGroups;
                    break;
            }

            let group = entries.get(scope);
            if (group === undefined) {
                group = [];
                entries.set(scope, group);
            }

            group.push([name, ptr(id)]);
        }

        return await Promise.all([
            this.traceNativeEntries("c", cGroups),
            this.traceNativeEntries("objc", objcGroups),
            this.traceNativeEntries("swift", swiftGroups),
        ]);
    }

    private async traceNativeEntries(
        flavor: "c" | "objc" | "swift",
        groups: NativeTargetScopes
    ) {
        if (groups.size === 0) {
            return;
        }

        const baseId = this.nextId;
        const scopes: HandlerRequestScope[] = [];
        const request: HandlerRequest = {
            type: "handlers:get",
            flavor,
            baseId,
            scopes,
        };
        for (const [name, items] of groups.entries()) {
            scopes.push({
                name,
                members: items.map((item) => item[0]),
            });
            this.nextId += items.length;
        }

        const { scripts }: HandlerResponse = await getHandlers(request);

        let offset = 0;
        for (const items of groups.values()) {
            for (const [name, address] of items) {
                const id = baseId + offset;
                const displayName = typeof name === "string" ? name : name[1];

                const handler = this.parseHandler(displayName, scripts[offset]);
                this.handlers.set(id, handler);

                try {
                    Interceptor.attach(
                        address,
                        this.makeNativeListenerCallbacks(id, handler)
                    );
                } catch (e: any) {
                    send({
                        type: "agent:warning",
                        message: `Skipping "${name}": ${e.message}`,
                    });
                }

                offset++;
            }
        }
    }

    private async traceJavaTargets(groups: JavaTargetGroup[]) {
        const baseId = this.nextId;
        const scopes: HandlerRequestScope[] = [];
        const request: HandlerRequest = {
            type: "handlers:get",
            flavor: "java",
            baseId,
            scopes,
        };
        for (const group of groups) {
            for (const [className, { methods }] of group.classes.entries()) {
                const classNameParts = className.split(".");
                const bareClassName = classNameParts[classNameParts.length - 1];
                const members: MemberName[] = Array.from(methods.keys()).map(
                    (bareName) => [bareName, `${bareClassName}.${bareName}`]
                );
                scopes.push({
                    name: className,
                    members,
                });
                this.nextId += members.length;
            }
        }

        const { scripts }: HandlerResponse = await getHandlers(request);

        return new Promise<void>((resolve) => {
            Java.perform(() => {
                let offset = 0;
                for (const group of groups) {
                    const factory = Java.ClassFactory.get(group.loader as any);

                    for (const [
                        className,
                        { methods },
                    ] of group.classes.entries()) {
                        const C = factory.use(className);

                        for (const [bareName, fullName] of methods.entries()) {
                            const id = baseId + offset;

                            const handler = this.parseHandler(
                                fullName,
                                scripts[offset]
                            );
                            this.handlers.set(id, handler);

                            const dispatcher: Java.MethodDispatcher =
                                C[bareName];
                            for (const method of dispatcher.overloads) {
                                method.implementation =
                                    this.makeJavaMethodWrapper(
                                        id,
                                        method,
                                        handler
                                    );
                            }

                            offset++;
                        }
                    }
                }

                resolve();
            });
        });
    }

    private makeNativeListenerCallbacks(
        id: TraceTargetId,
        handler: TraceHandler
    ): InvocationListenerCallbacks {
        const agent = this;

        return {
            onEnter(args) {
                agent.invokeNativeHandler(id, handler[0], this, args, ">");
            },
            onLeave(retval) {
                agent.invokeNativeHandler(id, handler[1], this, retval, "<");
            },
        };
    }

    private makeJavaMethodWrapper(
        id: TraceTargetId,
        method: Java.Method,
        handler: TraceHandler
    ): Java.MethodImplementation {
        const agent = this;

        return function (...args: any[]) {
            return agent.handleJavaInvocation(id, method, handler, this, args);
        };
    }

    private handleJavaInvocation(
        id: TraceTargetId,
        method: Java.Method,
        handler: TraceHandler,
        instance: Java.Wrapper,
        args: any[]
    ): any {
        this.invokeJavaHandler(id, handler[0], instance, args, ">");

        const retval = method.apply(instance, args);

        const replacementRetval = this.invokeJavaHandler(
            id,
            handler[1],
            instance,
            retval,
            "<"
        );

        return replacementRetval !== undefined ? replacementRetval : retval;
    }

    private invokeNativeHandler(
        id: TraceTargetId,
        callback: TraceEnterHandler | TraceLeaveHandler,
        context: InvocationContext,
        param: any,
        cutPoint: CutPoint
    ) {
        const timestamp = Date.now() - this.started;
        const threadId = context.threadId;
        const depth = this.updateDepth(threadId, cutPoint);

        const log = (...message: string[]) => {
            this.emit([id, timestamp, threadId, depth, message.join(" ")]);
        };

        callback.call(context, log, param, this.traceState);
    }

    private invokeJavaHandler(
        id: TraceTargetId,
        callback: TraceEnterHandler | TraceLeaveHandler,
        instance: Java.Wrapper,
        param: any,
        cutPoint: CutPoint
    ) {
        const timestamp = Date.now() - this.started;
        const threadId = Process.getCurrentThreadId();
        const depth = this.updateDepth(threadId, cutPoint);

        const log = (...message: string[]) => {
            this.emit([id, timestamp, threadId, depth, message.join(" ")]);
        };

        try {
            return callback.call(instance, log, param, this.traceState);
        } catch (e: any) {
            const isJavaException = e.$h !== undefined;
            if (isJavaException) {
                throw e;
            } else {
                Script.nextTick(() => {
                    throw e;
                });
            }
        }
    }

    private updateDepth(threadId: ThreadId, cutPoint: CutPoint): number {
        const depthEntries = this.stackDepth;

        let depth = depthEntries.get(threadId) ?? 0;
        if (cutPoint === ">") {
            depthEntries.set(threadId, depth + 1);
        } else {
            depth--;
            if (depth !== 0) {
                depthEntries.set(threadId, depth);
            } else {
                depthEntries.delete(threadId);
            }
        }

        return depth;
    }

    private parseHandler(name: string, script: string): TraceHandler {
        try {
            const h = (1, eval)("(" + script + ")");
            return [h.onEnter ?? noop, h.onLeave ?? noop];
        } catch (e: any) {
            send({
                type: "agent:warning",
                message: `Invalid handler for "${name}": ${e.message}`,
            });
            return [noop, noop];
        }
    }

    private includeModule(pattern: string, plan: TracePlan) {
        const { native } = plan;
        for (const m of this.getModuleResolver().enumerateMatches(
            `exports:${pattern}!*`
        )) {
            native.set(m.address.toString(), moduleFunctionTargetFromMatch(m));
        }
    }

    private excludeModule(pattern: string, plan: TracePlan) {
        const { native } = plan;
        for (const m of this.getModuleResolver().enumerateMatches(
            `exports:${pattern}!*`
        )) {
            native.delete(m.address.toString());
        }
    }

    private includeFunction(pattern: string, plan: TracePlan) {
        const e = parseModuleFunctionPattern(pattern);
        const { native } = plan;
        for (const m of this.getModuleResolver().enumerateMatches(
            `exports:${e.module}!${e.function}`
        )) {
            native.set(m.address.toString(), moduleFunctionTargetFromMatch(m));
        }
    }

    private excludeFunction(pattern: string, plan: TracePlan) {
        const e = parseModuleFunctionPattern(pattern);
        const { native } = plan;
        for (const m of this.getModuleResolver().enumerateMatches(
            `exports:${e.module}!${e.function}`
        )) {
            native.delete(m.address.toString());
        }
    }

    private includeRelativeFunction(pattern: string, plan: TracePlan) {
        const e = parseRelativeFunctionPattern(pattern);
        const address = Module.getBaseAddress(e.module).add(e.offset);
        plan.native.set(address.toString(), [
            "c",
            e.module,
            `sub_${e.offset.toString(16)}`,
        ]);
    }

    private includeImports(pattern: string, plan: TracePlan) {
        let matches: ApiResolverMatch[];
        if (pattern === null) {
            const mainModule = Process.enumerateModules()[0].path;
            matches = this.getModuleResolver().enumerateMatches(
                `imports:${mainModule}!*`
            );
        } else {
            matches = this.getModuleResolver().enumerateMatches(
                `imports:${pattern}!*`
            );
        }

        const { native } = plan;
        for (const m of matches) {
            native.set(m.address.toString(), moduleFunctionTargetFromMatch(m));
        }
    }

    private parseMethodPattern(pattern: string) {
        if (!pattern) {
            return [];
        }
        return pattern.replace(";", ",").split(",");
    }

    private includeObjCMethod(pattern: string, plan: TracePlan) {
        const { native } = plan;
        for (const pt of this.parseMethodPattern(pattern)) {
            for (const m of this.getObjcResolver().enumerateMatches(pt)) {
                native.set(m.address.toString(), objcMethodTargetFromMatch(m));
            }
        }
    }

    private excludeObjCMethod(pattern: string, plan: TracePlan) {
        const { native } = plan;
        for (const pt of this.parseMethodPattern(pattern)) {
            for (const m of this.getObjcResolver().enumerateMatches(pt)) {
                native.delete(m.address.toString());
            }
        }
    }

    private filterObjCMethod(pattern: string, plan: TracePlan) {
        const { native } = plan;
        const regList: Array<RegExp> = [];
        for (const pt of this.parseMethodPattern(pattern)) {
            try {
                const reg = new RegExp(pt, "g");
                regList.push(reg);
            } catch (error) {}
        }
        if (!regList.length) {
            return;
        }

        for (const [addr, [type, scope, name]] of native.entries()) {
            const displayName = typeof name === "string" ? name : name[1];
            let matched = false;
            for (const reg of regList) {
                if (reg.test(displayName)) {
                    matched = true;
                    break;
                }
            }
            if (!matched) {
                native.delete(addr);
            }
        }
    }

    private excludeObjCProperty(pattern: string, plan: TracePlan) {
        const { native } = plan;
        if (!pattern) {
            return;
        }
        const classNames = pattern.replace(";", ",").split(",");

        const capitalizeFirstLetter = (str: string) => {
            return str.replace(/^./, (str) => str.toUpperCase());
        };
        const propertyMethodNames: Array<string> = [];
        for (const className of classNames) {
            const cls = ObjC.classes[className];
            if (!cls || !cls.alloc) {
                continue;
            }
            try {
                const inst = cls.alloc().$ivars;
                const keys = Object.keys(inst);
                for (const key of keys) {
                    const name = key.substring(1);
                    const capitalName = capitalizeFirstLetter(name);
                    propertyMethodNames.push(`-[${className} ${name}]`);
                    propertyMethodNames.push(
                        `-[${className} set${capitalName}:]`
                    );
                }
            } catch (error) {}
        }
        const otherIgnoreSet = new Set(["cxx_destruct", "dealloc", "alloc"]);
        const methodNameSet = new Set(propertyMethodNames);
        for (const [addr, [type, scope, name]] of native.entries()) {
            const displayName = typeof name === "string" ? name : name[1];
            if (
                methodNameSet.has(displayName) ||
                otherIgnoreSet.has(displayName)
            ) {
                native.delete(addr);
            }
        }
    }

    private includeSwiftFunc(pattern: string, plan: TracePlan) {
        const { native } = plan;
        for (const m of this.getSwiftResolver().enumerateMatches(
            `functions:${pattern}`
        )) {
            native.set(m.address.toString(), swiftFuncTargetFromMatch(m));
        }
    }

    private excludeSwiftFunc(pattern: string, plan: TracePlan) {
        const { native } = plan;
        for (const m of this.getSwiftResolver().enumerateMatches(
            `functions:${pattern}`
        )) {
            native.delete(m.address.toString());
        }
    }

    private includeJavaMethod(pattern: string, plan: TracePlan) {
        const existingGroups = plan.java;

        const groups = Java.enumerateMethods(pattern);
        for (const group of groups) {
            const { loader } = group;

            const existingGroup = find(existingGroups, (candidate) => {
                const { loader: candidateLoader } = candidate;
                if (candidateLoader !== null && loader !== null) {
                    return candidateLoader.equals(loader);
                } else {
                    return candidateLoader === loader;
                }
            });
            if (existingGroup === undefined) {
                existingGroups.push(javaTargetGroupFromMatchGroup(group));
                continue;
            }

            const { classes: existingClasses } = existingGroup;
            for (const klass of group.classes) {
                const { name: className } = klass;

                const existingClass = existingClasses.get(className);
                if (existingClass === undefined) {
                    existingClasses.set(
                        className,
                        javaTargetClassFromMatchClass(klass)
                    );
                    continue;
                }

                const { methods: existingMethods } = existingClass;
                for (const methodName of klass.methods) {
                    const bareMethodName =
                        javaBareMethodNameFromMethodName(methodName);
                    const existingName = existingMethods.get(bareMethodName);
                    if (existingName === undefined) {
                        existingMethods.set(bareMethodName, methodName);
                    } else {
                        existingMethods.set(
                            bareMethodName,
                            methodName.length > existingName.length
                                ? methodName
                                : existingName
                        );
                    }
                }
            }
        }
    }

    private excludeJavaMethod(pattern: string, plan: TracePlan) {
        const existingGroups = plan.java;

        const groups = Java.enumerateMethods(pattern);
        for (const group of groups) {
            const { loader } = group;

            const existingGroup = find(existingGroups, (candidate) => {
                const { loader: candidateLoader } = candidate;
                if (candidateLoader !== null && loader !== null) {
                    return candidateLoader.equals(loader);
                } else {
                    return candidateLoader === loader;
                }
            });
            if (existingGroup === undefined) {
                continue;
            }

            const { classes: existingClasses } = existingGroup;
            for (const klass of group.classes) {
                const { name: className } = klass;

                const existingClass = existingClasses.get(className);
                if (existingClass === undefined) {
                    continue;
                }

                const { methods: existingMethods } = existingClass;
                for (const methodName of klass.methods) {
                    const bareMethodName =
                        javaBareMethodNameFromMethodName(methodName);
                    existingMethods.delete(bareMethodName);
                }
            }
        }
    }

    private includeDebugSymbol(pattern: string, plan: TracePlan) {
        const { native } = plan;
        for (const address of DebugSymbol.findFunctionsMatching(pattern)) {
            native.set(
                address.toString(),
                debugSymbolTargetFromAddress(address)
            );
        }
    }

    private emit(event: TraceEvent) {
        this.pendingEvents.push(event);

        if (this.flushTimer === null) {
            this.flushTimer = setTimeout(this.flush, 50);
        }
    }

    private flush = () => {
        if (this.flushTimer !== null) {
            clearTimeout(this.flushTimer);
            this.flushTimer = null;
        }

        if (this.pendingEvents.length === 0) {
            return;
        }

        const events = this.pendingEvents;
        this.pendingEvents = [];

        send({
            type: "events:add",
            events,
        });
    };

    private getModuleResolver(): ApiResolver {
        let resolver = this.cachedModuleResolver;
        if (resolver === null) {
            resolver = new ApiResolver("module");
            this.cachedModuleResolver = resolver;
        }
        return resolver;
    }

    private getObjcResolver(): ApiResolver {
        let resolver = this.cachedObjcResolver;
        if (resolver === null) {
            try {
                resolver = new ApiResolver("objc");
            } catch (e: any) {
                throw new Error("Objective-C runtime is not available");
            }
            this.cachedObjcResolver = resolver;
        }
        return resolver;
    }

    private getSwiftResolver(): ApiResolver {
        let resolver = this.cachedSwiftResolver;
        if (resolver === null) {
            try {
                resolver = new ApiResolver("swift" as ApiResolverType); // FIXME: Update typings.
            } catch (e: any) {
                throw new Error("Swift runtime is not available");
            }
            this.cachedSwiftResolver = resolver;
        }
        return resolver;
    }
}

async function getHandlers(request: HandlerRequest): Promise<HandlerResponse> {
    const scripts: HandlerScript[] = [];

    const { type, flavor, baseId } = request;

    const pendingScopes = request.scopes.slice().map(({ name, members }) => {
        return {
            name,
            members: members.slice(),
        };
    });
    let id = baseId;
    do {
        const curScopes: HandlerRequestScope[] = [];
        const curRequest: HandlerRequest = {
            type,
            flavor,
            baseId: id,
            scopes: curScopes,
        };

        let size = 0;
        for (const { name, members: pendingMembers } of pendingScopes) {
            const curMembers: MemberName[] = [];
            curScopes.push({
                name,
                members: curMembers,
            });

            let exhausted = false;
            for (const member of pendingMembers) {
                curMembers.push(member);

                size++;
                if (size === 1000) {
                    exhausted = true;
                    break;
                }
            }

            pendingMembers.splice(0, curMembers.length);

            if (exhausted) {
                break;
            }
        }

        while (
            pendingScopes.length !== 0 &&
            pendingScopes[0].members.length === 0
        ) {
            pendingScopes.splice(0, 1);
        }

        send(curRequest);
        const response: HandlerResponse = await receiveResponse(`reply:${id}`);

        scripts.push(...response.scripts);

        id += size;
    } while (pendingScopes.length !== 0);

    return {
        scripts,
    };
}

function receiveResponse<T>(type: string): Promise<T> {
    return new Promise((resolve) => {
        recv(type, (response: T) => {
            resolve(response);
        });
    });
}

function moduleFunctionTargetFromMatch(m: ApiResolverMatch): NativeTarget {
    const [modulePath, functionName] = m.name.split("!").slice(-2);
    return ["c", modulePath, functionName];
}

function objcMethodTargetFromMatch(m: ApiResolverMatch): NativeTarget {
    const { name } = m;
    const [className, methodName] = name
        .substr(2, name.length - 3)
        .split(" ", 2);

    const { method, methodName: methodNameWithPrefix } =
        runtime.methodFromAPI(m);
    const { argInfo, retType } = runtime.methdTypeSignatureOf(method.handle);
    let signature: MethodTypeSignature = {
        argInfo,
        retType,
        sel: `${method.selector}`,
    };
    return ["objc", className, [methodName, name, signature]];
}

function swiftFuncTargetFromMatch(m: ApiResolverMatch): NativeTarget {
    const { name } = m;
    const [modulePath, methodName] = name.split("!", 2);
    return ["swift", modulePath, methodName];
}

function debugSymbolTargetFromAddress(address: NativePointer): NativeTarget {
    const symbol = DebugSymbol.fromAddress(address);
    return ["c", symbol.moduleName ?? "", symbol.name!];
}

function parseModuleFunctionPattern(pattern: string) {
    const tokens = pattern.split("!", 2);

    let m, f;
    if (tokens.length === 1) {
        m = "*";
        f = tokens[0];
    } else {
        m = tokens[0] === "" ? "*" : tokens[0];
        f = tokens[1] === "" ? "*" : tokens[1];
    }

    return {
        module: m,
        function: f,
    };
}

function parseRelativeFunctionPattern(pattern: string) {
    const tokens = pattern.split("!", 2);

    return {
        module: tokens[0],
        offset: parseInt(tokens[1], 16),
    };
}

function javaTargetGroupFromMatchGroup(
    group: Java.EnumerateMethodsMatchGroup
): JavaTargetGroup {
    return {
        loader: group.loader,
        classes: new Map<JavaClassName, JavaTargetClass>(
            group.classes.map((klass) => [
                klass.name,
                javaTargetClassFromMatchClass(klass),
            ])
        ),
    };
}

function javaTargetClassFromMatchClass(
    klass: Java.EnumerateMethodsMatchClass
): JavaTargetClass {
    return {
        methods: new Map<JavaMethodName, JavaMethodNameOrSignature>(
            klass.methods.map((fullName) => [
                javaBareMethodNameFromMethodName(fullName),
                fullName,
            ])
        ),
    };
}

function javaBareMethodNameFromMethodName(fullName: string) {
    const signatureStart = fullName.indexOf("(");
    return signatureStart === -1
        ? fullName
        : fullName.substr(0, signatureStart);
}

function find<T>(
    array: T[],
    predicate: (candidate: T) => boolean
): T | undefined {
    for (const element of array) {
        if (predicate(element)) {
            return element;
        }
    }
}

function noop() {}

interface TraceScriptGlobals {
    stage: Stage;
    parameters: TraceParameters;
    state: TraceState;
}

type Stage = "early" | "late";

interface TraceParameters {
    [name: string]: any;
}

interface TraceState {
    [name: string]: any;
}

interface InitScript {
    filename: string;
    source: string;
}

type TraceSpec = TraceSpecItem[];
type TraceSpecItem = [TraceSpecOperation, TraceSpecScope, TraceSpecPattern];
type TraceSpecOperation = "include" | "exclude" | "filter";
type TraceSpecScope =
    | "module"
    | "function"
    | "relative-function"
    | "imports"
    | "objc-method"
    | "objc-property"
    | "swift-func"
    | "java-method"
    | "debug-symbol";
type TraceSpecPattern = string;

interface TracePlan {
    native: NativeTargets;
    java: JavaTargetGroup[];
}

type TargetType = "c" | "objc" | "swift" | "java";
type ScopeName = string;
type MemberName =
    | string
    | [string, string]
    | [string, string, MethodTypeSignature];

type NativeTargets = Map<NativeId, NativeTarget>;
type NativeTarget = ["c" | "objc" | "swift", ScopeName, MemberName];
type NativeTargetScopes = Map<ScopeName, NativeItem[]>;
type NativeItem = [MemberName, NativePointer];
type NativeId = string;

interface JavaTargetGroup {
    loader: Java.Wrapper | null;
    classes: Map<string, JavaTargetClass>;
}
interface JavaTargetClass {
    methods: Map<JavaMethodName, JavaMethodNameOrSignature>;
}
type JavaClassName = string;
type JavaMethodName = string;
type JavaMethodNameOrSignature = string;

interface HandlerRequest {
    type: "handlers:get";
    flavor: TargetType;
    baseId: TraceTargetId;
    scopes: HandlerRequestScope[];
}
interface HandlerRequestScope {
    name: string;
    members: MemberName[];
}
interface HandlerResponse {
    scripts: HandlerScript[];
}
type HandlerScript = string;

type TraceTargetId = number;
type TraceEvent = [TraceTargetId, Timestamp, ThreadId, Depth, Message];

type Timestamp = number;
type Depth = number;
type Message = string;

type TraceHandler = [TraceEnterHandler, TraceLeaveHandler];
type TraceEnterHandler = (
    log: LogHandler,
    args: any[],
    state: TraceState
) => void;
type TraceLeaveHandler = (
    log: LogHandler,
    retval: any,
    state: TraceState
) => any;

type CutPoint = ">" | "<";

type LogHandler = (...message: string[]) => void;

const agent = new Agent();

rpc.exports = {
    init: agent.init.bind(agent),
    dispose: agent.dispose.bind(agent),
    update: agent.update.bind(agent),
};
