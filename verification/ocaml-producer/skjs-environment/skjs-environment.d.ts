// The host environment SKJS's test harness checks its tests in, beyond the
// ECMAScript library TypeScript supplies, as `tsconfig.json` here gives it to
// the pipeline (DESIGN.md, "The SKJS test environment"). SKJS reads these names from its builtins stub
// (`import-stubs/@types/skjs/index.d.ts`), which replaces the library and so
// cannot be loaded beside it; each is restated here, as a global variable
// annotated with an interface, which the declaration reader reads at the
// members and call signatures a unit uses (DESIGN.md, "Global values"). Every
// declaration is a trusted assumption about the host, as an import's is.

/** `__SKJS_show(e, "T")` is SKJS's test assertion that it infers `T` for
 * `e`: a check of SKJS's inference, not of the program. As a value it is a
 * host function taking any value and an optional string and returning
 * `undefined`; what it asserts about `e`'s type is not read. */
interface SkjsShow {
  (value: unknown, expected?: string): void;
}
declare const __SKJS_show: SkjsShow;
declare const __SKJS_show_expanded: SkjsShow;

/** SKJS's closed object type: every key `T` does not name is absent. SKJS
 * gives the checker-reserved `SKJS_Closed` that meaning and states the
 * identity as its reading for tsc; that is the reading here. It promises less
 * than SKJS's, which is still true of every closed value, so a program
 * relying on the absence of other keys is refused, never admitted. */
type Closed<T> = T;

/** SKJS's dictionary alias, as its stub declares it. */
type StringRecord<V> = {
  [index: string]: V;
};

/** SKJS's stub for Node's `process`, with its members as SKJS declares them. */
interface SkjsProcessEnv {
  [key: string]: string | undefined;
  TZ?: string;
}
interface SkjsProcess {
  argv: string[];
  cwd(): string;
  env: SkjsProcessEnv;
  exit(status: number): never;
  on(event: string, listener: () => unknown): void;
}
declare const process: SkjsProcess;
