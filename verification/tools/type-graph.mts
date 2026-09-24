/** Exact native type graph. Mirrors PositiveNormalization.Clause / RequestJson.
 * Row indices are references, never unfolded trees; cycles need no special case.
 * A row and a label list both denote unions. Contracts within one clause are
 * simultaneous requirements (including all arrows of an overload).
 */
import type { PropertyKey } from "./declaration-types.mts";
export type Labels = number[];
/** A signature: the receiver a call may pass, then the parameters and the
 * result. A signature indifferent to its receiver names an unknown row. */
export type Arrow = [receiver: Labels, [domains: Labels[], result: Labels]];
/** An object contract: one label list per named field, in the order the
 * producer wrote them. Fields a contract does not name are unconstrained. */
export type Fields = [name: PropertyKey, labels: Labels][];
export type Tuple = {
  required: Labels[];
  optional: Labels[];
  rest: Labels | null;
  readonly: boolean;
};
export type Clause =
  | "nul"
  | "bool"
  | "undef"
  | "num"
  /** Semantic top: every value, and no operation through it. */
  | "top"
  | { boolLit: { value: boolean } }
  /** The double's bit pattern, decimal, as the consumer's UInt64. */
  | { numLit: { bits: string } }
  /** Strings, and one string, carried as itself. */
  | "str"
  | { strLit: { value: string } }
  /** Every bigint, and every symbol: opaque values. */
  | "bigint"
  | "symbol"
  /** `views` are read capabilities: a field read at a sound upper bound on
   * its contents, with no write permission through this contract. `optional`
   * fields constrain their key only where the object has it; the field is
   * left out when there are none. */
  | { refs: { first: Fields; rest: Fields[]; views: Fields; optional?: Fields } }
  /** Readonly string index views apply to every present own field. */
  | {
      dict: {
        first: Fields;
        rest: Fields[];
        views: Fields;
        indexes: Labels[];
        optional?: Fields;
      };
    }
  /** A tuple contract on an array store: required positions, optional
   * positions, and the rest, or null when no further position may exist. */
  | { list: { first: Tuple; rest: Tuple[] } }
  /** `variadic` signatures take any number of actuals past their fixed
   * parameters, each at the element contract; the field is left out when
   * there are none. */
  | { arrs: { arrows: Arrow[]; variadic?: RestArrow[] } }
  /** Construct signatures `[parameters, result]`: what a class meets. */
  | { ctors: { signatures: [Labels[], Labels][] } }
  | {
      callable: {
        first: Fields;
        rest: Fields[];
        arrows: Arrow[];
        variadic?: RestArrow[];
      };
    };
export type RestArrow = [
  receiver: Labels,
  [domains: Labels[], [element: Labels, result: Labels]],
];
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
  nul: "null",
  bool: "boolean",
  undef: "undefined",
  num: "number",
  str: "string",
  top: "unknown",
  bigint: "bigint",
  symbol: "symbol",
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

const isRecord = (v: unknown): v is Record<string, unknown> =>
  !!v && typeof v === "object" && !Array.isArray(v);
function obj(v: unknown, keys: string[]): Record<string, unknown> {
  if (
    !isRecord(v) ||
    Object.keys(v).length !== keys.length ||
    keys.some((k) => !(k in v))
  )
    throw Error("unexpected type graph fields");
  return v;
}
function objOptional(
  v: unknown,
  keys: string[],
  optional: string[],
): Record<string, unknown> {
  if (
    !isRecord(v) ||
    keys.some((k) => !(k in v)) ||
    Object.keys(v).some((k) => !keys.includes(k) && !optional.includes(k))
  )
    throw Error("unexpected type graph fields");
  return v;
}
function array(v: unknown): unknown[] {
  if (!Array.isArray(v)) throw Error("expected graph list");
  return v;
}
export function decodeLabels(v: unknown, size: number): Labels {
  if (
    array(v).some(
      (i) =>
        typeof i !== "number" || !Number.isSafeInteger(i) || i < 0 || i >= size,
    )
  )
    throw Error("type graph reference out of bounds");
  // Checked field by field above: this is where that becomes a type.
  return v as Labels;
}
export function decodeGraph(value: unknown): TypeGraph {
  const rows = array(value);
  const labels = (v: unknown) => decodeLabels(v, rows.length);
  const arrows = (v: unknown) =>
    array(v).forEach((a) => {
      const sig = array(a);
      if (sig.length !== 2) throw Error("expected a receiver and a signature");
      labels(sig[0]);
      const pair = array(sig[1]);
      if (pair.length !== 2) throw Error("expected arrow pair");
      array(pair[0]).forEach(labels);
      labels(pair[1]);
    });
  // Left out when empty: an explicit empty list is not the canonical form.
  const variadic = (v: unknown) => {
    const sigs = array(v);
    if (!sigs.length)
      throw Error("an empty variadic list is written by omitting it");
    sigs.forEach((s) => {
      const outer = array(s);
      if (outer.length !== 2)
        throw Error("expected a receiver and a signature");
      labels(outer[0]);
      const sig = array(outer[1]);
      if (sig.length !== 2) throw Error("expected a variadic signature");
      array(sig[0]).forEach(labels);
      const tail = array(sig[1]);
      if (tail.length !== 2) throw Error("expected an element and a result");
      labels(tail[0]);
      labels(tail[1]);
    });
  };
  const fields = (v: unknown) => {
    const names = new Set<string>();
    array(v).forEach((f) => {
      const pair = array(f);
      if (pair.length !== 2)
        throw Error("expected a field name and its labels");
      if (typeof pair[0] !== "string") throw Error("expected a field name");
      if (names.has(pair[0]))
        throw Error("duplicate field in an object contract");
      names.add(pair[0]);
      labels(pair[1]);
    });
  };
  const tuple = (v: unknown) => {
    const t = obj(v, ["required", "optional", "rest", "readonly"]);
    if (typeof t.readonly !== "boolean")
      throw Error("invalid tuple readonly flag");
    array(t.required).forEach(labels);
    array(t.optional).forEach(labels);
    if (t.rest !== null) labels(t.rest);
  };
  // One validator per clause kind. A missing key does not compile, so a new
  // clause cannot reach the decoder as a silent "unknown graph clause".
  // Keyed by the language's own union, so a clause added there and not here is
  // a type error; read by a key that may be none of them, so a clause this does
  // not know is a refusal rather than a silent pass.
  const check: Record<ClauseKey, (body: unknown) => void> &
    Record<string, ((body: unknown) => void) | undefined> = {
    boolLit: (b) => {
      if (typeof obj(b, ["value"]).value !== "boolean")
        throw Error("invalid Boolean literal");
    },
    // The identity is the double's bit pattern, decimal, as an unsigned 64.
    numLit: (b) => {
      const bits = obj(b, ["bits"]).bits;
      if (
        typeof bits !== "string" ||
        !/^[0-9]+$/.test(bits) ||
        BigInt(bits) > 0xffffffffffffffffn
      )
        throw Error("invalid numeric literal");
    },
    strLit: (b) => {
      if (typeof obj(b, ["value"]).value !== "string")
        throw Error("invalid string literal");
    },
    refs: (b) => {
      const r = objOptional(b, ["first", "rest", "views"], ["optional"]);
      fields(r.first);
      array(r.rest).forEach(fields);
      fields(r.views);
      if ("optional" in r) fields(r.optional);
    },
    dict: (b) => {
      const r = objOptional(b, ["first", "rest", "views", "indexes"], ["optional"]);
      fields(r.first);
      array(r.rest).forEach(fields);
      fields(r.views);
      array(r.indexes).forEach(labels);
      if ("optional" in r) fields(r.optional);
    },
    ctors: (b) => {
      array(obj(b, ["signatures"]).signatures).forEach((sig) => {
        const pair = array(sig);
        if (pair.length !== 2) throw Error("invalid construct signature");
        array(pair[0]).forEach(labels);
        labels(pair[1]);
      });
    },
    list: (b) => {
      const r = obj(b, ["first", "rest"]);
      tuple(r.first);
      array(r.rest).forEach(tuple);
    },
    arrs: (b) => {
      const r = objOptional(b, ["arrows"], ["variadic"]);
      arrows(r.arrows);
      if ("variadic" in r) variadic(r.variadic);
    },
    callable: (b) => {
      const r = objOptional(b, ["first", "rest", "arrows"], ["variadic"]);
      fields(r.first);
      array(r.rest).forEach(fields);
      arrows(r.arrows);
      if ("variadic" in r) variadic(r.variadic);
    },
  };

  rows.forEach((row) =>
    array(row).forEach((c) => {
      if (typeof c === "string") {
        if (!(c in STRING_CLAUSE_TEXT)) throw Error("unknown graph clause");
        return;
      }
      if (!isRecord(c)) throw Error("unknown graph clause");
      const key = Object.keys(c)[0];
      const validate = check[key];
      if (!validate) throw Error("unknown graph clause");
      validate(obj(c, [key])[key]);
    }),
  );
  // Checked field by field above: this is where that becomes a type.
  return value as TypeGraph;
}
/** JSON is the complete editable graph syntax; decoding is strict and lossless. */
export const parseGraph = (text: string): TypeGraph =>
  decodeGraph(JSON.parse(text));
export const printGraph = (graph: TypeGraph): string =>
  JSON.stringify(decodeGraph(graph), null, 2);
export const printLabels = (labels: Labels): string =>
  labels.length ? labels.map((l) => `#${l}`).join(" | ") : "never";
/** The receiver is shown as a `this` parameter; the graph's own rows carry no
 * name for "any receiver", so it is shown whatever it is. */
const receiverText = (receiver: Labels) => `this: ${printLabels(receiver)}`;
const arrowText = ([receiver, [domains, result]]: Arrow) =>
  `(${[receiverText(receiver), ...domains.map(printLabels)].join(", ")}) => ${printLabels(result)}`;
const restArrowText = ([receiver, [domains, [element, result]]]: RestArrow) =>
  `(${[receiverText(receiver), ...domains.map(printLabels), `...(${printLabels(element)})[]`].join(", ")}) => ${printLabels(result)}`;
const printTuple = (t: Tuple) =>
  `${t.readonly ? "readonly " : ""}[${[
    ...t.required.map(printLabels),
    ...t.optional.map((l) => `${printLabels(l)}?`),
    ...(t.rest ? [`...${printLabels(t.rest)}[]`] : []),
  ].join(", ")}]`;
/** A key as TypeScript writes it: a string plainly, a symbol by its index. */
export const keyText = (name: PropertyKey): string =>
  typeof name === "string" ? name : `[symbol ${name.symbol}]`;
const printFields = (fs: Fields) =>
  `ref{${fs.map(([name, ls]) => `${keyText(name)}: ${printLabels(ls)}`).join(", ")}}`;
function clauseText(c: Clause): string {
  if (typeof c === "string") return STRING_CLAUSE_TEXT[c];
  if ("boolLit" in c) return String(c.boolLit.value);
  // The reader shows the number, not the bit pattern that identifies it.
  if ("numLit" in c) return String(numberOfBits(c.numLit.bits));
  if ("strLit" in c) return JSON.stringify(c.strLit.value);
  if ("list" in c)
    return [c.list.first, ...c.list.rest].map(printTuple).join(" & ");
  if ("refs" in c)
    return [
      [c.refs.first, ...c.refs.rest].map(printFields).join(" & "),
      ...(c.refs.views.length ? [`readonly ${printFields(c.refs.views)}`] : []),
      ...(c.refs.optional?.length ? [`optional ${printFields(c.refs.optional)}`] : []),
    ].join(" & ");
  if ("dict" in c)
    return [
      [c.dict.first, ...c.dict.rest].map(printFields).join(" & "),
      ...(c.dict.views.length ? [`readonly ${printFields(c.dict.views)}`] : []),
      ...c.dict.indexes.map(
        (index) => `readonly {[key: string]: ${printLabels(index)}}`,
      ),
      ...(c.dict.optional?.length ? [`optional ${printFields(c.dict.optional)}`] : []),
    ].join(" & ");
  const calls = (arrows: Arrow[], variadic: RestArrow[] = []) =>
    `calls[${[...arrows.map(arrowText), ...variadic.map(restArrowText)].join("; ")}]`;
  if ("arrs" in c) return calls(c.arrs.arrows, c.arrs.variadic);
  if ("ctors" in c)
    return `new[${c.ctors.signatures.map(([ps, r]) => `(${ps.map(printLabels).join(", ")}) => ${printLabels(r)}`).join("; ")}]`;
  if ("callable" in c)
    return `object[${[c.callable.first, ...c.callable.rest].map(printFields).join(" & ")}; ${calls(c.callable.arrows, c.callable.variadic)}]`;
  return assertNever(c);
}
export interface GraphDefinition {
  label: string;
  definition: string;
}
/** Every row, exactly once. No fixed-label heuristics or depth limit. */
export const graphDefinitions = (graph: TypeGraph): GraphDefinition[] =>
  graph.map((row, i) => ({
    label: `#${i}`,
    definition: row.length ? row.map(clauseText).join(" | ") : "never",
  }));
