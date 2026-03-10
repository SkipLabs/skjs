import type {
  LevelWithSilent as LogLevel,
  LoggerOptions as PinoLoggerOptions,
} from "pino";

export type FastifyLoggerOptions = { level?: string };

export type FastifyServerOptions = {
  logger?: boolean | (FastifyLoggerOptions & PinoLoggerOptions);
};

export declare function fastify(opts: FastifyServerOptions): FastifyInstance;

// export { fastify as default };

export type LogFn = (obj: unknown, msg?: string) => void;

export interface FastifyBaseLogger_base {
  fatal: LogFn;
  error: LogFn;
  warn: LogFn;
  info: LogFn;
  debug: LogFn;
  trace: LogFn;
  silent: LogFn;
}

export interface FastifyBaseLogger extends FastifyBaseLogger_base {}

export interface FastifyRequest {
  id: string;
  //   params: RequestType['params']; // deferred inference
  //   raw: RawRequest;
  //   query: RequestType['query'];
  //   headers: RawRequest['headers'] & RequestType['headers'];
  log: FastifyBaseLogger;
  server: FastifyInstance;
  //   body: RequestType['body'];

  //   validationError?: Error & { validation: any; validationContext: string };

  //   readonly req: RawRequest & RouteGeneric['Headers']; // DEPRECATED
  readonly ip: string;
  readonly ips?: string[];
  readonly host: string;
  readonly port: number;
  readonly hostname: string;
  readonly url: string;
  readonly originalUrl: string;
  readonly protocol: "http" | "https";
  readonly method: string;
  //   readonly routeOptions: Readonly<RequestRouteOptions<ContextConfig, SchemaCompiler>>
  readonly is404: boolean;
  //   readonly socket: RawRequest['socket'];

  //   getValidationFunction(httpPart: HTTPRequestPart): ValidationFunction
  //   getValidationFunction(schema: { [key: string]: any }): ValidationFunction
  //   compileValidationSchema(schema: { [key: string]: any }, httpPart?: HTTPRequestPart): ValidationFunction
  //   validateInput(input: any, schema: { [key: string]: any }, httpPart?: HTTPRequestPart): boolean
  //   validateInput(input: any, httpPart?: HTTPRequestPart): boolean
  //   getDecorator<T>(name: string | symbol): T;
  //   setDecorator<T = unknown>(name: string | symbol, value: T): void;
}

export interface FastifyReply {
  //   readonly routeOptions: Readonly<RequestRouteOptions<ContextConfig, SchemaCompiler>>

  //   raw: RawReply;
  elapsedTime: number;
  log: FastifyBaseLogger;
  //   request: FastifyRequest<RouteGeneric, RawServer, RawRequest, SchemaCompiler, TypeProvider>;
  server: FastifyInstance;
  //   code<Code extends keyof SchemaCompiler['response'] extends never ? ReplyKeysToCodes<keyof RouteGeneric['Reply']> : keyof SchemaCompiler['response'] extends ReplyKeysToCodes<keyof RouteGeneric['Reply']> ? keyof SchemaCompiler['response'] : ReplyKeysToCodes<keyof RouteGeneric['Reply']>>(statusCode: Code): FastifyReply<RouteGeneric, RawServer, RawRequest, RawReply, ContextConfig, SchemaCompiler, TypeProvider, ResolveReplyTypeWithRouteGeneric<RouteGeneric['Reply'], Code, SchemaCompiler, TypeProvider>>;
  //   status<Code extends keyof SchemaCompiler['response'] extends never ? ReplyKeysToCodes<keyof RouteGeneric['Reply']> : keyof SchemaCompiler['response'] extends ReplyKeysToCodes<keyof RouteGeneric['Reply']> ? keyof SchemaCompiler['response'] : ReplyKeysToCodes<keyof RouteGeneric['Reply']>>(statusCode: Code): FastifyReply<RouteGeneric, RawServer, RawRequest, RawReply, ContextConfig, SchemaCompiler, TypeProvider, ResolveReplyTypeWithRouteGeneric<RouteGeneric['Reply'], Code, SchemaCompiler, TypeProvider>>;
  statusCode: number;
  sent: boolean;
  //   send(payload?: ReplyType): FastifyReply<RouteGeneric, RawServer, RawRequest, RawReply, ContextConfig, SchemaCompiler, TypeProvider>;
  //   header(key: HttpHeader, value: any): FastifyReply<RouteGeneric, RawServer, RawRequest, RawReply, ContextConfig, SchemaCompiler, TypeProvider>;
  //   headers(values: Partial<Record<HttpHeader, number | string | string[] | undefined>>): FastifyReply<RouteGeneric, RawServer, RawRequest, RawReply, ContextConfig, SchemaCompiler, TypeProvider>;
  //   getHeader(key: HttpHeader): number | string | string[] | undefined;
  //   getHeaders(): Record<HttpHeader, number | string | string[] | undefined>;
  //   removeHeader(key: HttpHeader): FastifyReply<RouteGeneric, RawServer, RawRequest, RawReply, ContextConfig, SchemaCompiler, TypeProvider>;
  //   hasHeader(key: HttpHeader): boolean;
  //   redirect(url: string, statusCode?: number): FastifyReply<RouteGeneric, RawServer, RawRequest, RawReply, ContextConfig, SchemaCompiler, TypeProvider>;
  //   writeEarlyHints(hints: StringRecord< string | string[]>, callback?: () => void): void;
  //   hijack(): FastifyReply<RouteGeneric, RawServer, RawRequest, RawReply, ContextConfig, SchemaCompiler, TypeProvider>;
  callNotFound(): void;
  //   type(contentType: string): FastifyReply<RouteGeneric, RawServer, RawRequest, RawReply, ContextConfig, SchemaCompiler, TypeProvider>;
  //   serializer(fn: (payload: any) => string): FastifyReply<RouteGeneric, RawServer, RawRequest, RawReply, ContextConfig, SchemaCompiler, TypeProvider>;
  //   serialize(payload: any): string | ArrayBuffer | Buffer;
  //   getSerializationFunction(httpStatus: string, contentType?: string): ((payload: { [key: string]: unknown }) => string) | undefined;
  //   getSerializationFunction(schema: { [key: string]: unknown }): ((payload: { [key: string]: unknown }) => string) | undefined;
  compileSerializationSchema(
    schema: { [key: string]: unknown },
    httpStatus?: string,
    contentType?: string,
  ): (payload: { [key: string]: unknown }) => string;
  //   serializeInput(input: { [key: string]: unknown }, schema: { [key: string]: unknown }, httpStatus?: string, contentType?: string): string;
  //   serializeInput(input: { [key: string]: unknown }, httpStatus: string, contentType?: string): unknown;
  then(fulfilled: () => void, rejected: (err: Error) => void): void;
  //   trailer: (
  //     key: string,
  //     fn: ((reply: FastifyReply<RouteGeneric, RawServer, RawRequest, RawReply, ContextConfig, SchemaCompiler, TypeProvider>, payload: string | Buffer | null) => Promise<string>) | ((reply: FastifyReply<RouteGeneric, RawServer, RawRequest, RawReply, ContextConfig, SchemaCompiler, TypeProvider>, payload: string | Buffer | null, done: (err: Error | null, value?: string) => void) => void)
  //   ) => FastifyReply<RouteGeneric, RawServer, RawRequest, RawReply, ContextConfig, SchemaCompiler, TypeProvider>;
  hasTrailer(key: string): boolean;
  //   removeTrailer(key: string): FastifyReply<RouteGeneric, RawServer, RawRequest, RawReply, ContextConfig, SchemaCompiler, TypeProvider>;
  //   getDecorator<T>(name: string | symbol): T;
}

export type onRequestAsyncHookHandler = (
  request: FastifyRequest,
  reply: FastifyReply,
) => Promise<unknown>;

export type FastifyPluginOptions = StringRecord<unknown>;

export type FastifyPluginAsync = (instance: FastifyInstance) => Promise<void>;

export type FastifyPluginCallback<Options /*extends FastifyPluginOptions*/> = (
  instance: FastifyInstance,
  opts: Options,
  done: (err?: Error) => void,
) => void;

export interface RegisterOptions {
  prefix?: string;
  logLevel?: LogLevel;
  logSerializers?: StringRecord<(value: unknown) => string>;
}

export type FastifyRegisterOptions<Options> =
  | (RegisterOptions & Options)
  | ((instance: FastifyInstance) => RegisterOptions & Options);

/* Wrong approximation of overloads */
export type FastifyRegister = <Options /*extends FastifyPluginOptions*/>(
  plugin: FastifyPluginAsync | FastifyPluginCallback<Options>,
  opts?: FastifyRegisterOptions<Options>,
) => SKJS_Ignorable<FastifyInstance>;

export interface FastifySchema {
  body?: unknown;
  querystring?: unknown;
  params?: unknown;
  headers?: unknown;
  response?: unknown;
}

export interface RouteShorthandOptions<SchemaCompiler extends FastifySchema> {
  schema?: SchemaCompiler;
}

export type RouteHandlerMethod = (
  /* this: FastifyInstance, */ request: FastifyRequest,
  reply: FastifyReply,
) => unknown | Promise<unknown> /* TODO */;

export type RouteShorthandMethod = <
  /* const */ SchemaCompiler extends FastifySchema,
>(
  path: string,
  opt: RouteShorthandOptions<SchemaCompiler>,
  handler: RouteHandlerMethod,
) => SKJS_Ignorable<FastifyInstance>;

export interface FastifyInstance {
  addHook(
    name: "onRequest" | "onResponse",
    // Luckily onRequestAsyncHookHandler and onResponseAsyncHookHandler are the same
    hook: onRequestAsyncHookHandler,
  ): SKJS_Ignorable<FastifyInstance>;

  register: FastifyRegister;

  delete: RouteShorthandMethod;
  get: RouteShorthandMethod;
  head: RouteShorthandMethod;
  patch: RouteShorthandMethod;
  post: RouteShorthandMethod;
  put: RouteShorthandMethod;
  options: RouteShorthandMethod;
  propfind: RouteShorthandMethod;
  proppatch: RouteShorthandMethod;
  mkcalendar: RouteShorthandMethod;
  mkcol: RouteShorthandMethod;
  copy: RouteShorthandMethod;
  move: RouteShorthandMethod;
  lock: RouteShorthandMethod;
  unlock: RouteShorthandMethod;
  trace: RouteShorthandMethod;
  report: RouteShorthandMethod;
  search: RouteShorthandMethod;
  all: RouteShorthandMethod;
}
