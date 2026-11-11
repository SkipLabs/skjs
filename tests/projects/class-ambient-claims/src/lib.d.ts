// An ambient class: declared in a .d.ts, so its instance type is structural
// (see skjs-rules.md rule 35). Any value with the members inhabits it,
// including arrays and functions that carry them.
export declare class Amb {
  a: number;
}
