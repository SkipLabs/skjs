import { AbstractEagerCollection, AbstractLazyCollection, Context, DepSafe, EagerCollection, Entry, Json, JsonObject, LazyCollection, LazyCompute, Mapper, Reducer, ServiceInstance, Values } from '@skipruntime/core';
import { JsonPartialObject, SkManaged } from '@skipruntime/core/json.js';
import { int } from '@skipruntime/core/std.js';

declare abstract class ALogger implements Logger {
	private category?;
	private level;
	constructor(level: Level, category?: string | undefined);
	debug(...args: unknown[]): void;
	trace(...args: unknown[]): void;
	info(...args: unknown[]): void;
	warn(...args: unknown[]): void;
	error(...args: unknown[]): void;
	fatal(...args: unknown[]): void;
	protected abstract log(message: string): void;
	private log_;
}
declare class DataTester<K extends Json, V extends Json> extends AbstractLazyCollection {
	protected readonly data: Map<string, {
		key: K;
		values: Array<V & DepSafe>;
	}>;
	set(key: K, value: V & DepSafe): void;
	setArray(key: K, values: Array<V & DepSafe>): void;
	getArray(key: K): Array<V & DepSafe>;
	getUnique(key: K, default_?: {
		ifNone?: (V & DepSafe) | undefined;
		ifMany?: (V & DepSafe) | undefined;
	}): V & DepSafe;
	protected sortedStringify_: (obj: unknown) => string;
}
export declare class ArrayValues<T extends Json> implements Values<T> {
	private values;
	constructor(values: Array<T & DepSafe>);
	getUnique(default_?: {
		ifMany?: T & DepSafe;
	}): T & DepSafe;
	toArray(): Array<T & DepSafe>;
	[Symbol.iterator](): Iterator<T & DepSafe>;
}
export declare class AuthenticationError extends Error {
}
export declare class CodeError extends Error {
	code: number;
	error: string;
	contentType?: string | undefined;
	constructor(code: number, error: string, contentType?: string | undefined);
}
export declare class ConflictError extends Error {
}
export declare class ConsoleLogger extends ALogger {
	protected log(message: string): void;
}
export declare class ContextTester extends SkManaged implements Context {
	private resources;
	private logger?;
	constructor(resources?: EagerCollection<{
		name: string;
		params: Json;
	}, number>, logger?: Logger | undefined);
	createLazyCollection<K extends Json, V extends Json, Params extends readonly DepSafe[]>(computeCts: new (...params: Params) => LazyCompute<K, V>, ...params: Params): LazyCollection<K, V>;
	useExternalResource<K extends Json, V extends Json>(_resource: {
		service: string;
		identifier: string;
		params?: Json;
	}): EagerCollection<K, V>;
	jsonExtract(_value: JsonObject, _pattern: string): Json[];
	activeResources(): EagerCollection<{
		name: string;
		params: Json;
	}, int>;
	debug(...args: unknown[]): void;
	error(...args: unknown[]): void;
	warn(...args: unknown[]): void;
	info(...args: unknown[]): void;
	fatal(...args: unknown[]): void;
	trace(...args: unknown[]): void;
}
export declare class EagerTester<K extends Json, V extends Json> extends AbstractEagerCollection implements EagerCollection<K, V> {
	protected readonly data: Map<string, {
		key: K;
		values: Array<V & DepSafe>;
	}>;
	set(key: K, value: V & DepSafe): void;
	setArray(key: K, values: Array<V & DepSafe>): void;
	getArray(key: K): Array<V & DepSafe>;
	getUnique(key: K, default_?: {
		ifNone?: (V & DepSafe) | undefined;
		ifMany?: (V & DepSafe) | undefined;
	}): V & DepSafe;
	protected sortedStringify_: (obj: unknown) => string;
	map<K2 extends Json, V2 extends Json, Params extends readonly DepSafe[]>(mapperCst: new (...params: Params) => Mapper<K, V, K2, V2>, ...params: Params): EagerCollection<K2, V2>;
	reduce<Accum extends Json, Params extends readonly DepSafe[]>(reducerCst: new (...params: Params) => Reducer<V, Accum>, ...params: Params): EagerCollection<K, Accum>;
	mapReduce<K2 extends Json, V2 extends Json, MapperParams extends readonly DepSafe[]>(mapper: new (...params: MapperParams) => Mapper<K, V, K2, V2>, ...mapperParams: MapperParams): <Accum extends Json, ReducerParams extends readonly DepSafe[]>(reducer: new (...params: ReducerParams) => Reducer<V2, Accum>, ...reducerParams: ReducerParams) => EagerCollection<K2, Accum>;
	private compare_;
	slice(start: K & DepSafe, end: K & DepSafe): EagerCollection<K, V>;
	slices(...ranges: [
		K & DepSafe,
		K & DepSafe
	][]): EagerCollection<K, V>;
	take(limit: int): EagerCollection<K, V>;
	merge(...others: EagerCollection<K, V>[]): EagerCollection<K, V>;
	size(): number;
	private keys_;
}
export declare class EntryTestNotifier<K extends Json, V extends Json> {
	private checker;
	private updates;
	private error?;
	private waiting?;
	private close_?;
	private constructor();
	static make<K extends Json, V extends Json>(subscribe: (update: (v: () => Array<Entry<K, V>>, init: boolean) => void) => Promise<{
		readonly close: () => void;
	}>, checker: <T>(e: Expectation<T>) => Promise<void>, log?: boolean): Promise<EntryTestNotifier<K, V>>;
	check(values: Entry<K, V>[], init: boolean): Promise<void>;
	checkInit(values: Entry<K, V>[]): Promise<void>;
	checkUpdate(values: Entry<K, V>[]): Promise<void>;
	checkEmpty(): {
		type: string;
		actual: number;
		expected: number;
	};
	wait(timeout?: number): Promise<void>;
	close(): void;
}
export declare class FileLogger extends ALogger {
	private sync;
	private logFile;
	constructor(logDir: string, level: Level, logName: string, category?: string, sync?: boolean);
	protected log(message: string): void;
}
export declare class ForbiddenError extends Error {
}
export declare class InvalidParameterError extends Error {
}
export declare class LazyDataTester<K extends Json, V extends Json> extends DataTester<K, V> implements LazyCollection<K, V> {
}
export declare class LazyTester<K extends Json, V extends Json> extends AbstractLazyCollection implements LazyCollection<K, V> {
	private compute;
	private readonly context;
	constructor(compute: LazyCompute<K, V>);
	getArray(key: K): (V & DepSafe)[];
	getUnique(key: K, default_?: {
		ifNone?: (V & DepSafe) | undefined;
		ifMany?: (V & DepSafe) | undefined;
	}): V & DepSafe;
}
export declare class NotFoundError extends Error {
}
export declare class SkipRedirect {
	code: number;
	url: string;
	constructor(code: number, url: string);
}
export declare class SkipResponse<T = undefined> {
	status: number;
	body: T;
	headers?: {
		[name: string]: string;
	} | undefined;
	etag?: string | undefined;
	lastModified?: Date | undefined;
	contentType?: string | undefined;
	constructor(status: number, body: T, headers?: {
		[name: string]: string;
	} | undefined, etag?: string | undefined, lastModified?: Date | undefined, contentType?: string | undefined);
}
export declare class StreamerResult {
	close: () => Return<void>;
	constructor(close: () => Return<void>);
}
export declare class TestNotifier<V extends Json> {
	private checker;
	private updates;
	private error?;
	private waiting?;
	private close_?;
	private constructor();
	static make<V extends Json>(subscribe: (init: (v: DataInit<V>) => void, update: (v: DataUpdate<V>) => void) => Promise<{
		readonly close: () => void;
	}>, checker: <T>(e: Expectation<T>) => Promise<void>, log?: boolean): Promise<TestNotifier<V>>;
	check(values: DataInit<V> | DataUpdate<V>): Promise<void>;
	checkInit(values: DataInit<V>): Promise<void>;
	checkUpdate(values: DataUpdate<V>): Promise<void>;
	checkEmpty(): {
		type: string;
		actual: number;
		expected: number;
	};
	wait(timeout?: number): Promise<void>;
	close(): void;
}
export declare const CONNECT: Method;
export declare const DELETE: Method;
export declare const GET: Method;
export declare const HEAD: Method;
export declare const OPTIONS: Method;
export declare const PATCH: Method;
export declare const POST: Method;
export declare const PUT: Method;
export declare const TRACE: Method;
export declare const levelIndexed: LevelIndexed;
export declare const packageNameRegex: RegExp;
export declare function availablePortRangeGetter(minPort: number, maxPort: number): () => Promise<{
	control_port: number;
	streaming_port: number;
	release: () => void;
}>;
export declare function availablePortsInRange(minPort: number, maxPort: number, number: number): Promise<{
	ports: Array<number>;
	release: () => void;
}>;
export declare function buildCacheControlHeader(cache: CacheControl): string;
export declare function castBranded<T extends string>(value: string): T;
export declare function checkCache<T extends Json | undefined>(headers: {
	[name: string]: string;
}, response: SkipResponse<T>): SkipResponse<T>;
export declare function checkLevel(level: string): Level;
export declare function configCors(cors: CorsConfig, headers: (name: string, value: string) => void, origin?: string): void;
export declare function copyDir(src: string, dest: string): Promise<void>;
export declare function expectArrayWith<T>(value: unknown, name: string, checker: (v: unknown, path: string) => T, path?: string): T[];
export declare function expectAuthString(value: unknown, path?: string): string;
export declare function expectBearerToken(value: unknown, path?: string): string;
export declare function expectBoolean(value: unknown, path?: string): boolean;
export declare function expectBranded<T extends string>(value: unknown, path?: string): T;
export declare function expectEntriesWith<K extends Json, V extends Json>(value: unknown, keyChecker: (v: unknown, path: string) => K, valueChecker: (v: unknown, path: string) => V, path?: string): Array<Entry<K, V>>;
export declare function expectEntryWith<K extends Json, V extends Json>(value: unknown, keyChecker: (v: unknown, path: string) => K, valueChecker: (v: unknown, path: string) => V, path?: string): Entry<K, V>;
export declare function expectNotNull(value: unknown, path?: string): Json;
export declare function expectNullOr<T>(value: unknown, checker: (v: unknown, path: string) => T, path?: string): T | null;
export declare function expectNumber(value: unknown, path?: string): number;
export declare function expectObject<T>(value: unknown, path?: string): Record<string, T>;
export declare function expectOr<T>(value: unknown, name: string, checker1: (v: unknown, path: string) => T, checker2: (v: unknown, path: string) => T, path?: string): T;
export declare function expectPatternString<T extends string>(value: unknown, name: string, pattern: RegExp, path?: string): T;
export declare function expectPositiveNumber(value: unknown, path?: string): number;
export declare function expectRecordWith<K extends string | number, V>(value: unknown, name: string, keyChecker: (v: unknown, path: string) => K, valueChecker: (v: unknown, path: string) => V, path?: string): Record<K, V>;
export declare function expectSet<T extends string | number>(value: unknown, name: string, values: Set<T>, path?: string): T;
export declare function expectString(value: unknown, path?: string): string;
export declare function expectStringArray(value: unknown, path?: string): Array<string>;
export declare function expectStringFormat(value: unknown, format: string, path?: string): string;
export declare function expectStringOrBoolean(value: unknown, path?: string): boolean;
export declare function expectStringOrNumber(value: unknown, path?: string): number;
export declare function expectUndefinedOr<T>(value: unknown, checker: (v: unknown, path: string) => T, path?: string): T | undefined;
export declare function extractCookie(cookieHeader: string | undefined, name: string): string | null;
export declare function fileExists(path: string): Promise<boolean>;
/**
 * Formats a single argument to string representation
 * @returns -
 */
export declare function formatArg(arg: unknown): string;
/**
 * Formats multiple arguments into a single string
 * @returns -
 */
export declare function formatArgs(...args: unknown[]): string;
/**
 * Formats a log message with metadata
 *
 * @param message - Main log message
 * @param options - Formatting options
 * @returns Formatted log string
 *
 * @example
 * format("User logged in", { level: "info", category: "auth" })
 * // => "[2025-01-16T10:30:45.123Z] [INFO] [auth] User logged in"
 */
export declare function formatLog(message: string, options?: FormatOptions): string;
/**
 * Simple string formatting using indexed placeholders {1}, {2}, etc.
 *
 * @param template - Format string with {1}, {2}, {3}... placeholders (1-indexed)
 * @param args - Values to substitute
 * @returns Formatted string
 *
 * @example
 * format("Hello {1}, you have {2} messages", "Alice", 5)
 * // => "Hello Alice, you have 5 messages"
 *
 * format("User {1} logged in at {2}", "Bob", new Date())
 * // => "User Bob logged in at 2025-01-16T10:30:45.123Z"
 *
 * format("Data: {1}", { name: "test", value: 42 })
 * // => "Data: { \"name\": \"test\", \"value\": 42 }"
 */
export declare function formatString(template: string, ...args: unknown[]): string;
export declare function getErrorMessage(error: unknown): string;
export declare function getFileContent(path: string, encoding?: "utf-8" | null): Promise<string | undefined>;
export declare function invertUTF8String(key: string): string;
export declare function isDirectory(path: string): Promise<boolean>;
/**
 * Symmetric companion of `isJsonObject`. Same TS-narrowing rationale —
 * the `value is readonly Json[]` annotation narrows the union the way
 * `Array.isArray` alone does not.
 */
export declare function isJsonArray(value: Json): value is readonly Json[];
/**
 * Narrow a `Json` value to its object variants (`JsonObject` /
 * `JsonPartialObject`). Sole reason this exists: a bare
 * `Array.isArray(v)` guard does NOT narrow against `readonly Json[]`
 * inside a `Json` union — `Array.isArray` is typed as `value is any[]`
 * and TS does not equate `any[]` with `readonly Json[]`, so a check
 * like `if (Array.isArray(v)) return …` leaves the array variant in
 * the union afterwards. Passing the value through this predicate
 * works because the user-defined `value is JsonObject | JsonPartialObject`
 * signature lets TS strip the array variant explicitly.
 */
export declare function isJsonObject(value: Json): value is JsonObject | JsonPartialObject;
export declare function listFiles(dir: string, recurse?: boolean): Promise<string[]>;
export declare function lookupTests(servicePackage?: string): Promise<CategorizedTests>;
export declare function manageEntriesStream<K extends Json, V extends Json>(url: string, update: (v: () => Array<Entry<K, V>>, init: boolean) => void, keyChecker: (v: unknown, path: string) => K, valueChecker: (v: unknown, path: string) => V): Promise<{
	readonly close: () => void;
}>;
export declare function manageStream<K extends Json>(url: string, init: (v: Array<K>) => void, update: (v: {
	updated: Array<K>;
	deleted: Array<string>;
}) => void, checker: (v: unknown, path: string) => K, params: {
	[name: string]: Json | null;
}, headers?: {
	[name: string]: string;
}): Promise<{
	readonly close: () => void;
}>;
export declare function message(path: string, expected: unknown, value: unknown): string;
export declare function moveFile(src: string, dest: string): Promise<void>;
export declare function runSkipRuntimeSuite(ports: {
	control_port: number;
	streaming?: {
		port: number;
		direct: boolean;
	};
}, logger?: (...args: unknown[]) => void): Promise<() => void>;
/**
 * Order routes so that, at every path-segment position, a literal
 * segment is registered before a parameterised one. Express matches the
 * first registered handler that fits a request, so this ordering is
 * what guarantees a hit on `/pages/X/revisions/diff` reaches its own
 * handler instead of being captured by `/pages/{pageId}/revisions/{revisionNumber}`
 * (where `:revisionNumber` would greedily accept the literal `diff`).
 *
 * Segment-by-segment comparison: at the first divergence, literal beats
 * parameter; if both literal or both parameter, lexicographic. The
 * previous implementation treated *any* path containing `{` as dynamic
 * and compared the WHOLE path with `localeCompare` — which sorted by
 * the locale-dependent ordering of `{` vs letters and silently broke
 * the literal-first invariant whenever two paths share an early
 * parameter (e.g. both start with `/pages/{pageId}/`).
 */
export declare function sortCommands<T extends Command>(routes: T[]): T[];
export declare function splitPath(p: string): string[];
export declare function subscribe<K extends Json, V extends Json, P extends Json, ID extends Json>(service: ServiceInstance, streamId: string, convert: (entries: Array<Entry<K, V>>) => Array<P>, getid: (entry: Entry<K, V>) => ID, stream: SkipStream, onInit: () => void): () => void;
export declare function subscribeSingle<K extends Json, V extends Json, P extends Json>(service: ServiceInstance, streamId: string, convert: (entry: Entry<K, V>) => P, stream: SkipStream, onInit: () => void): () => void;
export declare function tryParseJson<T>(content: string, label: string): ParseResult<T>;
export declare function validate<T>(value: unknown, validator: (v: unknown, p?: string) => T): T;
export declare function waitAndDetach(child: ChildProcess, test: (stdout: string, stderr: string) => boolean, logger?: (...args: unknown[]) => void): Promise<() => void>;
export interface AuthenticationChecker<T, C> {
	check(token: string, context: C): Promise<T>;
}
export interface ChildProcess {
	stdout: Readable;
	stderr: Readable;
	readonly pid?: number;
	readonly exitCode: number | null;
	kill(signal?: string | number): boolean;
	unref(): void;
	ref(): void;
	on<T extends Array<unknown>>(event: string, listener: (...args: T) => void): this;
	on(event: "disconnect", listener: () => void): this;
	on(event: "error", listener: (err: Error) => void): this;
	on(event: "exit", listener: (code: number | null, signal: string | null) => void): this;
}
export interface Command {
	readonly method: Method;
	readonly path: string;
	readonly accepted?: string[];
	readonly cache?: CacheControl;
}
/**
 * Formats a log message with optional timestamp and level
 */
export interface FormatOptions {
	/** Log level (info, warn, error, log) */
	level?: Level;
	/** Include timestamp (default: true) */
	timestamp?: boolean;
	/** Custom timestamp format function */
	timestampFormat?: (date: Date) => string;
	/** Include level prefix (default: true) */
	includeLevel?: boolean;
	/** Category/namespace for the log */
	category?: string;
}
export interface HeadersAuthenticationChecker<T, C> {
	check(header: {
		[name: string]: string;
	}, context: C): Promise<T>;
}
export interface Logger {
	debug: (...args: unknown[]) => void;
	error: (...args: unknown[]) => void;
	warn: (...args: unknown[]) => void;
	info: (...args: unknown[]) => void;
	fatal: (...args: unknown[]) => void;
	trace: (...args: unknown[]) => void;
}
export interface Loggers<N extends Namespaces> {
	debug: (category: N[number], ...args: unknown[]) => void;
	error: (category: N[number], ...args: unknown[]) => void;
	warn: (category: N[number], ...args: unknown[]) => void;
	info: (category: N[number], ...args: unknown[]) => void;
	fatal: (category: N[number], ...args: unknown[]) => void;
	trace: (category: N[number], ...args: unknown[]) => void;
}
export interface Readable {
	on<T extends Array<unknown>>(event: string, listener: (...args: T) => void): this;
	setEncoding(encoding: string): this;
}
export interface SkipStream {
	write(data: StreamData): void;
	close(): void;
}
export interface SkipStreamer {
	stream(stream: SkipStream, onInit: (status: number) => void): Return<StreamerResult>;
}
export type ArrayExpectation<T> = CompareUnsorted<T> | CheckContains<T> | CheckNotContains<T>;
export type CacheControl = {
	maxAge?: number;
	sMaxAge?: number;
	private?: boolean;
	public?: boolean;
	noCache?: boolean;
	noStore?: boolean;
	mustRevalidate?: boolean;
	proxyRevalidate?: boolean;
	immutable?: boolean;
	staleWhileRevalidate?: number;
	staleIfError?: number;
};
export type CategorizedTests = {
	[categorie: string]: TestInfo;
};
export type CheckContains<T> = {
	readonly type: "Contains";
	readonly actual: Array<T>;
	readonly expected: T;
};
export type CheckFalsy<T> = {
	readonly type: "Falsy";
	readonly actual: T;
};
export type CheckInstanceOf<T> = {
	readonly type: "ToBeA";
	readonly actual: T;
	readonly cst: new (...args: unknown[]) => T;
};
export type CheckMatch = {
	readonly type: "Match";
	readonly actual: string;
	readonly pattern: RegExp | string;
};
export type CheckNotContains<T> = {
	readonly type: "NotContains";
	readonly actual: Array<T>;
	readonly expected: T;
};
export type CheckNotMatch = {
	readonly type: "NotMatch";
	readonly actual: string;
	readonly pattern: RegExp | string;
};
export type CheckNotThrows = {
	readonly type: "NotThrows";
	readonly fn: () => void;
};
export type CheckNotToBeRejected = {
	readonly type: "NotToBeRejected";
	readonly fn: () => Promise<void>;
};
export type CheckThrows = {
	readonly type: "Throws";
	readonly fn: () => void;
	readonly errorType?: new <T>(...args: T[]) => Error;
	readonly errorMessage?: string | RegExp;
};
export type CheckToBeRejected = {
	readonly type: "ToBeRejected";
	readonly fn: () => Promise<void>;
	readonly errorType?: new (...args: Array<unknown>) => Error;
	readonly errorMessage?: string | RegExp;
};
export type CheckTruthy<T> = {
	readonly type: "Truthy";
	readonly actual: T;
};
export type Checkers = {
	value: <T>(e: Expectation<T>) => Promise<void>;
	array: <T>(e: ArrayExpectation<T>) => Promise<void>;
};
export type Compare<T> = {
	readonly type: "Equal" | "NotEqual";
	readonly actual: T;
	readonly expected: T;
};
export type CompareNumeric = {
	readonly type: "GreaterThan" | "LessThan" | "GreaterThanOrEqual" | "LessThanOrEqual";
	readonly actual: number;
	readonly expected: number;
};
export type CompareUnsorted<T> = {
	readonly type: "EqualUnsorted";
	readonly actual: Array<T>;
	readonly expected: Array<T>;
};
export type CorsConfig = {
	allowOrigins?: string[] | "*" | ((origin: string) => boolean);
	allowMethods?: Method[] | "*";
	allowHeaders?: string[] | "*";
	exposeHeaders?: string[];
	allowCredentials?: boolean;
	maxAge?: number;
};
export type DataInit<V extends Json> = Array<V>;
export type DataUpdate<V extends Json> = {
	updated: Array<V>;
	deleted: Array<string>;
};
export type EntryUpdate<K extends Json, V extends Json> = [
	Entry<K, V>[],
	boolean
];
export type Expectation<T> = Compare<T> | CheckTruthy<T> | CheckFalsy<T> | CheckThrows | CheckNotThrows | CompareNumeric | CheckMatch | CheckNotMatch | CheckInstanceOf<T> | CheckToBeRejected | CheckNotToBeRejected;
export type HttpHeaders = {
	[name: string]: string | string[] | undefined;
};
export type Level = "debug" | "trace" | "info" | "warn" | "error" | "fatal";
export type LevelIndexed = {
	debug: 0;
	trace: 1;
	info: 2;
	warn: 3;
	error: 4;
	fatal: 5;
};
export type Method = WithoutBody | WithBody;
export type Namespaces = string[];
/**
 * Result-typed JSON parse for code that runs at process startup.
 *
 * The generated server's index.ts reads sidecar JSON files
 * (external-access.json, ui-pages.json) before binding any route.
 * A bare JSON.parse on a truncated or corrupted file would crash
 * the server with an uncaught SyntaxError before useful work
 * begins. tryParseJson lets the caller branch on parse success
 * explicitly — fatal for required artefacts, recoverable for
 * optional ones — without scattering try/catch through each
 * startup site.
 */
export type ParseResult<T> = {
	readonly ok: true;
	readonly value: T;
} | {
	readonly ok: false;
	readonly error: string;
};
export type PartialObject = {
	[key: string]: Json | null | undefined;
};
export type RestService = {
	readonly commands: Command[];
	readonly options?: RestServiceOptions;
};
export type RestServiceOptions = {
	readonly port?: number;
	readonly cors?: () => CorsConfig | false;
	readonly healthcheck?: string;
	readonly openapiJson?: string;
	readonly indexHtml?: string;
	readonly htmlPages?: {
		readonly [path: string]: string;
	};
	readonly googleClientId?: string | null;
};
export type Return<T> = T | Promise<T>;
export type Route<R> = {
	readonly perform: (params: unknown, body: unknown, query: unknown, headers: HttpHeaders) => Promise<SkipResult<R>>;
	readonly method: Method;
	readonly path: string;
	readonly accepted?: string[];
	readonly cache?: CacheControl;
};
export type SkipResult<T = undefined> = SkipResponse<T> | SkipRedirect | SkipStreamer;
export type StreamData = {
	event: string;
	id: string;
	data: string;
};
export type Test = {
	name: string;
	check: (checkers: Checkers) => Return<void>;
	timeout?: number;
};
export type TestInfo = {
	readonly tests: Array<Test>;
	readonly prerequisite?: () => Return<() => Return<void>>;
};
export type TestType = "Equal" | "EqualUnsorted" | "EqualExactly" | "NotEqual" | "Truthy" | "Falsy" | "Throws" | "NotThrows" | "Contains" | "NotContains" | "GreaterThan" | "LessThan" | "GreaterThanOrEqual" | "LessThanOrEqual" | "Match" | "NotMatch" | "ToBeA" | "ToBeRejected" | "NotToBeRejected";
export type WithBody = "PUT" | "POST" | "PATCH";
export type WithoutBody = "GET" | "HEAD" | "OPTIONS" | "TRACE" | "DELETE" | "CONNECT";

export {
	Json,
	JsonObject,
};

export {};
