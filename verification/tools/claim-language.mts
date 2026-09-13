/** Structural claim language at the producer/viewer boundary.
 * Source annotations use the same types. Runtime data is decoded before it is
 * accepted as text; unsupported producer shapes stay in the raw JSON editor.
 */
export interface WireType { top: boolean; atoms: Atom[] }
export interface Field { name: string; optional: boolean; read: WireType; write: WireType }
export interface RecordAtom {
  a: "record"; fields: Field[];
  indexes: { string: string; number: string; symbol: string };
  call: string; construct: string; array: string; and?: Atom[];
}
export interface FunctionAtom {
  a: "function"; params: WireType[]; result: WireType;
  construct: string; array: string; and?: Atom[];
}
export type Atom =
  | { a: "null" | "undefined" | "boolean" | "string" | "number" }
  | { a: "stringlit" | "numberlit" | "booleanlit"; v: string }
  | RecordAtom | FunctionAtom
  | { a: "callable"; function: FunctionAtom; bag: RecordAtom };

function object(v: unknown): Record<string, unknown> {
  if (!v || typeof v !== "object" || Array.isArray(v)) throw Error("expected an object");
  return v as Record<string, unknown>;
}
function keys(v: Record<string, unknown>, required: string[], optional: string[] = []) {
  if (required.some(k => !(k in v)) || Object.keys(v).some(k => ![...required,...optional].includes(k)))
    throw Error("unexpected or missing claim field");
}
function list(v: unknown): unknown[] { if (!Array.isArray(v)) throw Error("expected a list"); return v; }
function str(v: unknown) { if (typeof v !== "string") throw Error("expected a string"); }
function bool(v: unknown) { if (typeof v !== "boolean") throw Error("expected a boolean"); }
function atom(v: unknown): void {
  const o = object(v);
  switch (o.a) {
    case "null": case "undefined": case "boolean": case "string": case "number": keys(o,["a"]); break;
    case "booleanlit": case "numberlit": case "stringlit":
      keys(o,["a","v"]); str(o.v);
      if (o.a === "booleanlit" && o.v !== "true" && o.v !== "false") throw Error("invalid boolean literal");
      if (o.a === "numberlit" && !Number.isFinite(Number(o.v))) throw Error("invalid number literal");
      break;
    case "record": {
      keys(o,["a","fields","indexes","call","construct","array"],["and"]);
      const names = new Set();
      for (const f of list(o.fields)) {
        const field = object(f); keys(field,["name","optional","read","write"]);
        str(field.name); bool(field.optional); decodeClaimType(field.read); decodeClaimType(field.write);
        if (names.has(field.name)) throw Error("duplicate field"); names.add(field.name);
      }
      const indexes = object(o.indexes); keys(indexes,["string","number","symbol"]);
      Object.values(indexes).forEach(str); str(o.call); str(o.construct); str(o.array);
      if (o.and !== undefined) list(o.and).forEach(atom);
      break;
    }
    case "function":
      keys(o,["a","params","result","construct","array"],["and"]);
      list(o.params).forEach(decodeClaimType); decodeClaimType(o.result); str(o.construct); str(o.array);
      if (o.and !== undefined) list(o.and).forEach(atom);
      break;
    case "callable":
      keys(o,["a","function","bag"]); atom(o.function); atom(o.bag);
      if (object(o.function).a !== "function" || object(o.bag).a !== "record") throw Error("invalid callable");
      break;
    default: throw Error("unknown claim atom");
  }
}
export function decodeClaimType(v: unknown): WireType {
  const o = object(v); keys(o,["top","atoms"]); bool(o.top); list(o.atoms).forEach(atom);
  if (o.top && list(o.atoms).length) throw Error("unknown cannot also carry atoms");
  return v as WireType;
}
