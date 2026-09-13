/** Exact native type graph. Mirrors PositiveNormalization.Clause / RequestJson.
 * Row indices are references, never unfolded trees; cycles need no special case.
 * A row and a label list both denote unions. Contracts within one clause are
 * simultaneous requirements (including all arrows of an overload).
 */
export type Labels = number[];
export type Arrow = [domains: Labels[], result: Labels];
export type Clause = "nul" | "bool" | "undef"
  | { boolLit: { value: boolean } }
  | { refs: { first: Labels; rest: Labels[] } }
  | { arrs: { arrows: Arrow[] } }
  | { callable: { first: Labels; rest: Labels[]; arrows: Arrow[] } };
export type Row = Clause[];
export type TypeGraph = Row[];

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
  rows.forEach(row => array(row).forEach(c => {
    if (c === "nul" || c === "bool" || c === "undef") return;
    if (!c || typeof c !== "object" || Array.isArray(c)) throw Error("unknown graph clause");
    const key = Object.keys(c)[0]; const o = obj(c,[key]);
    if (key === "boolLit") {
      if (typeof obj(o[key],["value"]).value !== "boolean") throw Error("invalid Boolean literal");
    } else if (key === "refs" || key === "callable") {
      const r = obj(o[key],key === "refs" ? ["first","rest"] : ["first","rest","arrows"]);
      labels(r.first); array(r.rest).forEach(labels); if (key === "callable") arrows(r.arrows);
    } else if (key === "arrs") arrows(obj(o[key],["arrows"]).arrows);
    else throw Error("unknown graph clause");
  }));
  return value as TypeGraph;
}
/** JSON is the complete editable graph syntax; decoding is strict and lossless. */
export const parseGraph = (text: string): TypeGraph => decodeGraph(JSON.parse(text));
export const printGraph = (graph: TypeGraph): string => JSON.stringify(decodeGraph(graph),null,2);
export const printLabels = (labels: Labels): string => labels.length ? labels.map(l => `#${l}`).join(" | ") : "never";
const arrowText = ([domains,result]: Arrow) => `(${domains.map(printLabels).join(", ")}) => ${printLabels(result)}`;
function clauseText(c: Clause): string {
  if (typeof c === "string") return {nul:"null",bool:"boolean",undef:"undefined"}[c];
  if ("boolLit" in c) return String(c.boolLit.value);
  if ("refs" in c) return [c.refs.first,...c.refs.rest].map(a => `ref(${printLabels(a)})`).join(" & ");
  if ("arrs" in c) return `calls[${c.arrs.arrows.map(arrowText).join("; ")}]`;
  return `object[${[c.callable.first,...c.callable.rest].map(a => `value: ${printLabels(a)}`).join(" & ")}; calls[${c.callable.arrows.map(arrowText).join("; ")}]]`;
}
export interface GraphDefinition { label: string; definition: string }
/** Every row, exactly once. No fixed-label heuristics or depth limit. */
export const graphDefinitions = (graph: TypeGraph): GraphDefinition[] => graph.map((row,i) => ({
  label:`#${i}`, definition: row.length ? row.map(clauseText).join(" | ") : "never",
}));
