/** Native term syntax, matching Calculus.lean and its derived JSON codec. The
 * program graph over these terms is its own language, in control-flow.mts. */
export type Tag =
  | "isNul"
  | "isBool"
  | "isRef"
  | "isFun"
  | "isUndef"
  | "isNullish"
  | "isNum"
  | "isStr"
  | "isBigint"
  | "isSymbol"
  | "truthy"
  | "isArray"
  | { numEq: { bits: string } }
  | { strEq: { value: string } }
  | { boolEq: { value: boolean } }
  /** A bigint singleton, as its integer: a JSON number of any length. */
  | { bigintEq: { value: number } };
/** An object's invocation code: none, a closure, variadic code collecting
 * further actuals, or `.bind`'s forwarding descriptor, which keeps the target,
 * the receiver and the argument prefix it was given. */
export type CallCode =
  | "absent"
  | { closure: { arity: number; body: Term } }
  | { variadic: { fixed: number; body: Term } }
  | { bound: { target: Term; receiver: Term; pre: Term[] } };
export type Term =
  | "nul"
  | "undef"
  | "tru"
  | "fls"
  /** A number, as the bit pattern of the double it denotes: its identity. */
  | { num: { bits: string } }
  /** A string, as itself. */
  | { str: { value: string } }
  /** A bigint, as its integer: a JSON number of any length. */
  | { bigint: { value: number } }
  | { var: { i: number } }
  /** Invoke `f` with the receiver `r` and the actuals `args`. */
  | { invoke: { f: Term; r: Term; args: Term[] } }
  | { letE: { a: Term; b: Term } }
  | { objAt: { fields: [string, number][]; call: CallCode } }
  | { makeAt: { call: CallCode; names: string[]; inits: Term[] } }
  | { readAt: { field: string; a: Term } }
  | { indexAt: { a: Term; key: Term } }
  | { writeAt: { field: string; a: Term; b: Term } }
  | { test: { k: Tag; a: Term } }
  | { ite: { c: Term; t: Term; e: Term } }
  /** A binary operator on primitive operands: arithmetic on two numbers or
   * two bigints, or a relational comparison. */
  | { arith: { op: (typeof OPERATORS)[number]; a: Term; b: Term } }
  /** An array store with these initial elements, in order: the value an
   * array object holds in its store field. */
  | { arrLit: { inits: Term[] } }
  /** The element of a store at a numeric index: `undefined` at a hole or out
   * of range. */
  | { elemAt: { a: Term; i: Term } }
  /** The store with the element at a numeric index set, growing it when the
   * index is past the end. */
  | { setElem: { a: Term; i: Term; v: Term } }
  /** The length of a store, as a number. */
  | { lenOf: { a: Term } }
  /** A store: the location of each element, in order, or none at a hole. */
  | { arr: { elems: (number | null)[] } }
  /** An actual standing for the elements of a store, read where it is written. */
  | { spread: { a: Term } }
  /** Evaluate `a`, then throw its value. */
  | { throw: { a: Term } };
/** Every binary operator, as `Arith` in Calculus.lean names them. */
const OPERATORS = ["add", "sub", "mul", "div", "pow", "xor", "rem", "lt", "le", "gt", "ge", "eq"] as const;
/** Every tag, checked against `Tag`: adding one there and not here is a type
 * error rather than an "unknown tag" at run time. */
const TAGS: Record<Extract<Tag, string>, true> = {
  isNul: true,
  isBool: true,
  isRef: true,
  isFun: true,
  isUndef: true,
  isNullish: true,
  isNum: true,
  isStr: true,
  isBigint: true,
  isSymbol: true,
  truthy: true,
  isArray: true,
};
const tags: readonly unknown[] = Object.keys(TAGS);
/** Whether a decoded value is a tag, so the table above stays the one place a
 * tag is declared even for readers of other languages that carry one. */
export function isTag(v: unknown): v is Tag {
  if (tags.includes(v)) return true;
  if (!isRecord(v) || Object.keys(v).length !== 1) return false;
  if (isRecord(v.strEq))
    return (
      Object.keys(v.strEq).length === 1 && typeof v.strEq.value === "string"
    );
  if (isRecord(v.boolEq))
    return (
      Object.keys(v.boolEq).length === 1 && typeof v.boolEq.value === "boolean"
    );
  if (isRecord(v.bigintEq))
    return (
      Object.keys(v.bigintEq).length === 1 && typeof v.bigintEq.value === "number"
    );
  if (!isRecord(v.numEq)) return false;
  const n = v.numEq;
  return (
    Object.keys(n).length === 1 &&
    typeof n.bits === "string" &&
    /^[0-9]+$/.test(n.bits) &&
    BigInt(n.bits) <= 0xffffffffffffffffn
  );
}
/* JSON shape checks, shared with the program graph in control-flow.mts. They
 * belong to neither language, so they name neither: a malformed target is not
 * a malformed term. */
const isRecord = (v: unknown): v is Record<string, unknown> =>
  !!v && typeof v === "object" && !Array.isArray(v);
export function fields(v: unknown, keys: string[]): Record<string, unknown> {
  if (
    !isRecord(v) ||
    Object.keys(v).length !== keys.length ||
    keys.some((k) => !(k in v))
  )
    throw Error("unexpected or missing field");
  return v;
}
export function nat(v: unknown) {
  if (typeof v !== "number" || !Number.isSafeInteger(v) || v < 0)
    throw Error("expected a non-negative integer");
}
function code(v: unknown) {
  if (v === "absent") return;
  const key = isRecord(v) ? Object.keys(v)[0] : undefined;
  if (key === "closure") {
    const c = fields(fields(v, ["closure"]).closure, ["arity", "body"]);
    nat(c.arity);
    decodeTerm(c.body);
  } else if (key === "variadic") {
    const c = fields(fields(v, ["variadic"]).variadic, ["fixed", "body"]);
    nat(c.fixed);
    decodeTerm(c.body);
  } else if (key === "bound") {
    const c = fields(fields(v, ["bound"]).bound, ["target", "receiver", "pre"]);
    decodeTerm(c.target);
    decodeTerm(c.receiver);
    if (!Array.isArray(c.pre)) throw Error("invalid bound prefix");
    c.pre.forEach(decodeTerm);
  } else throw Error("unknown call code");
}
/** The terms that are all tag and no fields, which is how they are written. */
const BARE: Record<Extract<Term, string>, true> = {
  nul: true,
  undef: true,
  tru: true,
  fls: true,
};
const bare: readonly unknown[] = Object.keys(BARE);
const isBareTerm = (v: unknown): v is Extract<Term, string> => bare.includes(v);
type KeysOf<T> = T extends unknown ? keyof T : never;
type TermKey = KeysOf<Exclude<Term, string>>;

export function decodeTerm(value: unknown): Term {
  if (isBareTerm(value)) return value;
  if (!value || typeof value !== "object") throw Error("invalid term");
  const key = Object.keys(value)[0],
    outer = fields(value, [key]);
  // One entry per compound constructor of `Term`; a missing key is a type error.
  // Keyed by the language's own union, so a constructor added there and not
  // here is a type error; read by a key that may be none of them, so a
  // constructor this does not know is a refusal.
  const shape: Record<TermKey, string[]> &
    Record<string, string[] | undefined> = {
    num: ["bits"],
    str: ["value"],
    bigint: ["value"],
    var: ["i"],
    invoke: ["f", "r", "args"],
    letE: ["a", "b"],
    objAt: ["fields", "call"],
    makeAt: ["call", "names", "inits"],
    readAt: ["field", "a"],
    indexAt: ["a", "key"],
    writeAt: ["field", "a", "b"],
    test: ["k", "a"],
    ite: ["c", "t", "e"],
    arith: ["op", "a", "b"],
    arrLit: ["inits"],
    elemAt: ["a", "i"],
    setElem: ["a", "i", "v"],
    lenOf: ["a"],
    arr: ["elems"],
    spread: ["a"],
    throw: ["a"],
  };
  const keys = shape[key];
  if (!keys) throw Error("unknown term constructor");
  const o = fields(outer[key], keys);
  for (const [k, v] of Object.entries(o)) {
    // A number's identity is its double's bit pattern, decimal, unsigned 64.
    if (k === "bits") {
      if (
        typeof v !== "string" ||
        !/^[0-9]+$/.test(v) ||
        BigInt(v) > 0xffffffffffffffffn
      )
        throw Error("invalid number");
    } else if (k === "value" && key === "bigint") {
      if (typeof v !== "number" || !Number.isInteger(v)) throw Error("invalid bigint");
    } else if (k === "value") {
      if (typeof v !== "string") throw Error("invalid string");
    } else if (k === "i" || k === "l") nat(v);
    else if (k === "call") code(v);
    else if (k === "k") {
      if (!isTag(v)) throw Error("unknown tag");
    } else if (k === "field") {
      if (typeof v !== "string") throw Error("invalid field name");
    } else if (k === "names") {
      if (!Array.isArray(v) || v.some((n) => typeof n !== "string"))
        throw Error("invalid field names");
    } else if (k === "fields") {
      if (!Array.isArray(v)) throw Error("invalid object fields");
      for (const pair of v) {
        if (
          !Array.isArray(pair) ||
          pair.length !== 2 ||
          typeof pair[0] !== "string"
        )
          throw Error("invalid object field");
        nat(pair[1]);
      }
    } else if (k === "op") {
      if (!OPERATORS.some((op) => op === v))
        throw Error("unknown binary operator");
    } else if (k === "elems") {
      if (!Array.isArray(v)) throw Error("invalid store");
      for (const l of v) if (l !== null) nat(l);
    } else if (k === "args" || k === "inits") {
      if (!Array.isArray(v)) throw Error("invalid arguments");
      v.forEach(decodeTerm);
    } else decodeTerm(v);
  }
  // Checked field by field above: this is where that becomes a type.
  return value as Term;
}
export const parseTerm = (text: string): Term => decodeTerm(JSON.parse(text));
export const printTerm = (term: Term): string =>
  JSON.stringify(decodeTerm(term));
