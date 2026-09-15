/** Exact native type graph. Mirrors PositiveNormalization.Clause / RequestJson.
 * Row indices are references, never unfolded trees; cycles need no special case.
 * A row and a label list both denote unions. Contracts within one clause are
 * simultaneous requirements (including all arrows of an overload).
 */
export type Labels = number[];
export type Arrow = [domains: Labels[], result: Labels];
export type Clause = "nul" | "bool" | "undef" | "num"
  | { boolLit: { value: boolean } }
  /** The double's bit pattern, decimal, as the consumer's UInt64. */
  | { numLit: { bits: string } }
  | { refs: { first: Labels; rest: Labels[] } }
  | { arrs: { arrows: Arrow[] } }
  | { callable: { first: Labels; rest: Labels[]; arrows: Arrow[] } };
export type Row = Clause[];
export type TypeGraph = Row[];

/** The clause kinds, split so that every consumer can be made to cover them.
 * `keyof` over a union intersects, so the key extraction distributes. */
export type StringClause = Extract<Clause, string>;
type ObjectClause = Exclude<Clause, string>;
type KeysOf<T> = T extends unknown ? keyof T : never;
export type ClauseKey = KeysOf<ObjectClause>;

/** Adding a clause to `Clause` without adding it here is a compile error, and
 * these are the only two places a clause kind is enumerated. */
export const STRING_CLAUSE_TEXT: Record<StringClause, string> = {
  nul: "null", bool: "boolean", undef: "undefined", num: "number",
};

/** The number a literal's bit pattern denotes. Readers show the number; the
 * bits are its identity, not its display. */
export const numberOfBits = (bits: string): number => {
  const view = new DataView(new ArrayBuffer(8));
  view.setBigUint64(0, BigInt(bits));
  return view.getFloat64(0);
};

/** Unreachable when every clause kind is handled; a compile error when one is
 * added and a dispatch above is not extended to cover it. */
export function assertNever(x: never): never {
  throw Error(`unhandled type graph clause: ${JSON.stringify(x)}`);
}

function obj(v: unknown, keys: string[]): Record<string, unknown> {
  if (!v || typeof v !== "object" || Array.isArray(v) ||
      Object.keys(v).length !== keys.length || keys.some(k => !(k in v)))
    throw Error("unexpected type graph fields");
  return v as Record<string, unknown>;
}
function array(v: unknown): unknown[] { if (!Array.isArray(v)) throw Error("expected graph list"); return v; }
export function decodeLabels(v: unknown, size: number): Labels {
  if (array(v).some(i => !Number.isSafeInteger(i) || (i as number) < 0 || (i as number) >= size))
    throw Error("type graph reference out of bounds");
  return v as Labels;
}
export function decodeGraph(value: unknown): TypeGraph {
  const rows = array(value);
  const labels = (v: unknown) => decodeLabels(v,rows.length);
  const arrows = (v: unknown) => array(v).forEach(a => {
    const pair = array(a); if (pair.length !== 2) throw Error("expected arrow pair");
    array(pair[0]).forEach(labels); labels(pair[1]);
  });
  // One validator per clause kind. A missing key does not compile, so a new
  // clause cannot reach the decoder as a silent "unknown graph clause".
  const check: Record<ClauseKey, (body: unknown) => void> = {
    boolLit: b => {
      if (typeof obj(b,["value"]).value !== "boolean") throw Error("invalid Boolean literal");
    },
    // The identity is the double's bit pattern, decimal, as an unsigned 64.
    numLit: b => {
      const bits = obj(b,["bits"]).bits;
      if (typeof bits !== "string" || !/^[0-9]+$/.test(bits) ||
          BigInt(bits) > 0xffffffffffffffffn)
        throw Error("invalid numeric literal");
    },
    refs: b => { const r = obj(b,["first","rest"]); labels(r.first); array(r.rest).forEach(labels); },
    arrs: b => arrows(obj(b,["arrows"]).arrows),
    callable: b => {
      const r = obj(b,["first","rest","arrows"]);
      labels(r.first); array(r.rest).forEach(labels); arrows(r.arrows);
    },
  };
  const validators = check as Record<string, ((body: unknown) => void) | undefined>;
  rows.forEach(row => array(row).forEach(c => {
    if (typeof c === "string") {
      if (!(c in STRING_CLAUSE_TEXT)) throw Error("unknown graph clause");
      return;
    }
    if (!c || typeof c !== "object" || Array.isArray(c)) throw Error("unknown graph clause");
    const key = Object.keys(c)[0];
    const validate = validators[key];
    if (!validate) throw Error("unknown graph clause");
    validate(obj(c,[key])[key]);
  }));
  return value as TypeGraph;
}
/** JSON is the complete editable graph syntax; decoding is strict and lossless. */
export const parseGraph = (text: string): TypeGraph => decodeGraph(JSON.parse(text));
export const printGraph = (graph: TypeGraph): string => JSON.stringify(decodeGraph(graph),null,2);
export const printLabels = (labels: Labels): string => labels.length ? labels.map(l => `#${l}`).join(" | ") : "never";
const arrowText = ([domains,result]: Arrow) => `(${domains.map(printLabels).join(", ")}) => ${printLabels(result)}`;
function clauseText(c: Clause): string {
  if (typeof c === "string") return STRING_CLAUSE_TEXT[c];
  if ("boolLit" in c) return String(c.boolLit.value);
  // The reader shows the number, not the bit pattern that identifies it.
  if ("numLit" in c) return String(numberOfBits(c.numLit.bits));
  if ("refs" in c) return [c.refs.first,...c.refs.rest].map(a => `ref(${printLabels(a)})`).join(" & ");
  if ("arrs" in c) return `calls[${c.arrs.arrows.map(arrowText).join("; ")}]`;
  if ("callable" in c)
    return `object[${[c.callable.first,...c.callable.rest].map(a => `value: ${printLabels(a)}`).join(" & ")}; calls[${c.callable.arrows.map(arrowText).join("; ")}]]`;
  return assertNever(c);
}
export interface GraphDefinition { label: string; definition: string }
/** Every row, exactly once. No fixed-label heuristics or depth limit. */
export const graphDefinitions = (graph: TypeGraph): GraphDefinition[] => graph.map((row,i) => ({
  label:`#${i}`, definition: row.length ? row.map(clauseText).join(" | ") : "never",
}));
