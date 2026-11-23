declare const f: { (x: string): number; a: "" } & { a: number };
// @skjs-expect-error This expression was expected to be of type 'void'
// @skjs-expect-error Too few arguments for this call
f();
