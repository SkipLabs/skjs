/** Native term syntax, matching Language.lean and its derived JSON codec. */
export type Tag = "isNul" | "isBool" | "isRef" | "isFun" | "isUndef" | "isNullish" | "isNum";
export type CallCode = "absent" | {closure: {arity: number; body: Term}};
export type Term = "nul" | "undef" | "tru" | "fls"
  /** A number, as the bit pattern of the double it denotes: its identity. */
  | {num: {bits: string}}
  | {var: {i: number}} | {call: {f: Term; args: Term[]}}
  | {letE: {a: Term; b: Term}} | {obj: {l: number; call: CallCode}}
  | {make: {call: CallCode; a: Term}} | {read: {a: Term}}
  | {write: {a: Term; b: Term}} | {test: {k: Tag; a: Term}}
  | {ite: {c: Term; t: Term; e: Term}};
/** Every tag, checked against `Tag`: adding one there and not here is a type
 * error rather than an "unknown tag" at run time. */
const TAGS: Record<Tag, true> = {
  isNul: true, isBool: true, isRef: true, isFun: true,
  isUndef: true, isNullish: true, isNum: true,
};
const tags: string[] = Object.keys(TAGS);
function fields(v: unknown, keys: string[]): Record<string, unknown> {
  if (!v || typeof v !== "object" || Array.isArray(v) || Object.keys(v).length !== keys.length || keys.some(k => !(k in v))) throw Error("invalid term fields");
  return v as Record<string, unknown>;
}
function nat(v: unknown) { if (!Number.isSafeInteger(v) || (v as number) < 0) throw Error("invalid term index"); }
function code(v: unknown) {
  if (v === "absent") return;
  const c = fields(fields(v,["closure"]).closure,["arity","body"]); nat(c.arity); decodeTerm(c.body);
}
type KeysOf<T> = T extends unknown ? keyof T : never;
type TermKey = KeysOf<Exclude<Term, string>>;

export function decodeTerm(value: unknown): Term {
  if (["nul","undef","tru","fls"].includes(value as string)) return value as Term;
  if (!value || typeof value !== "object") throw Error("invalid term");
  const key = Object.keys(value)[0], outer = fields(value,[key]);
  // One entry per compound constructor of `Term`; a missing key is a type error.
  const shape: Record<TermKey,string[]> = {num:["bits"],var:["i"],call:["f","args"],letE:["a","b"],obj:["l","call"],make:["call","a"],read:["a"],write:["a","b"],test:["k","a"],ite:["c","t","e"]};
  const keys = (shape as Record<string,string[]|undefined>)[key];
  if (!keys) throw Error("unknown term constructor");
  const o = fields(outer[key],keys);
  for (const [k,v] of Object.entries(o)) {
    // A number's identity is its double's bit pattern, decimal, unsigned 64.
    if (k === "bits") {
      if (typeof v !== "string" || !/^[0-9]+$/.test(v) || BigInt(v) > 0xffffffffffffffffn)
        throw Error("invalid number");
    }
    else if (k === "i" || k === "l") nat(v);
    else if (k === "call") code(v);
    else if (k === "k") { if (!tags.includes(v as string)) throw Error("unknown tag"); }
    else if (k === "args") { if (!Array.isArray(v)) throw Error("invalid arguments"); v.forEach(decodeTerm); }
    else decodeTerm(v);
  }
  return value as Term;
}
export const parseTerm = (text: string): Term => decodeTerm(JSON.parse(text));
export const printTerm = (term: Term): string => JSON.stringify(decodeTerm(term));

export interface Target { label: number; mapping: number[] | null }
export type Continuation = "ret"
  | {bind: {next: Target}} | {effect: {next: Target}}
  | {branch: {yes: Target; no: Target}}
  | {branchBind: {yes: Target; no: Target}}
  | {tagBind: {test: Tag; yes: Target; no: Target}};
export interface ProgramNode { expression: Term; continuation: Continuation }
export function decodeTarget(value: unknown): Target {
  const t = fields(value,["label","mapping"]); nat(t.label);
  if (t.mapping !== null) {
    if (!Array.isArray(t.mapping)) throw Error("invalid slot mapping");
    t.mapping.forEach(nat);
  }
  return value as Target;
}
export function decodeNode(value: unknown): ProgramNode {
  const n = fields(value,["expression","continuation"]); decodeTerm(n.expression);
  if (n.continuation === "ret") return value as ProgramNode;
  if (!n.continuation || typeof n.continuation !== "object") throw Error("invalid continuation");
  const k = Object.keys(n.continuation)[0], outer = fields(n.continuation,[k]);
  switch (k) {
    case "bind": case "effect": decodeTarget(fields(outer[k],["next"]).next); break;
    case "branch": case "branchBind": case "tagBind": {
      const c = fields(outer[k], k === "tagBind" ? ["test","yes","no"] : ["yes","no"]);
      decodeTarget(c.yes); decodeTarget(c.no);
      if (k === "tagBind" && !tags.includes(c.test as string)) throw Error("invalid tag");
      break;
    }
    default: throw Error("unknown continuation");
  }
  return value as ProgramNode;
}
