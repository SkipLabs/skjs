import { FastifyPluginCallback, FastifyRequest } from "fastify";

type OriginCallback = (
  err: Error | null,
  origin: ValueOrArray<OriginType>,
) => void;
type OriginType = string | boolean | RegExp;
type ValueOrArray<T> = T | ArrayOfValueOrArray<T>;

type ArrayOfValueOrArray<T> = Array<ValueOrArray<T>>;

type FastifyCorsPlugin = FastifyPluginCallback<NonNullable<FastifyCorsOptions>>;
/*| FastifyCorsOptionsDelegate*/

type FastifyCorsHook =
  | "onRequest"
  | "preParsing"
  | "preValidation"
  | "preHandler"
  | "preSerialization"
  | "onSend";

export type OriginFunction = (
  origin: string | undefined,
  callback: OriginCallback,
) => void;

export interface FastifyCorsOptions {
  hook?: FastifyCorsHook;
  delegator?: FastifyCorsOptionsDelegate;
  origin?: ValueOrArray<OriginType> | OriginFunction;
  credentials?: boolean;
  exposedHeaders?: string | string[];
  allowedHeaders?: string | string[];
  methods?: string | string[];
  maxAge?: number;
  cacheControl?: number | string;
  preflightContinue?: boolean;
  optionsSuccessStatus?: number;
  preflight?: boolean;
  strictPreflight?: boolean;
  hideOptionsRoute?: boolean;
}

export type FastifyCorsOptionsDelegateCallback = (
  req: FastifyRequest,
  cb: (error: Error | null, corsOptions?: FastifyCorsOptions) => void,
) => void;
export type FastifyCorsOptionsDelegatePromise = (
  req: FastifyRequest,
) => Promise<FastifyCorsOptions>;
export type FastifyCorsOptionsDelegate =
  | FastifyCorsOptionsDelegateCallback
  | FastifyCorsOptionsDelegatePromise;

export declare const fastifyCors: FastifyCorsPlugin;

export { fastifyCors as default };
