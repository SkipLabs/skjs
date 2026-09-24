/* Surface text for the claim language declared in claim.mts, printed and read
 * back here so reports and the editor share one syntax. @ followed by a JSON
 * object states nondefault object modes and conjunction metadata explicitly.
 * The text always determines its type. */
import {
  decodeClaimType,
  type Atom,
  type ClaimType,
  type Field,
  type FunctionAtom,
  type RecordAtom,
} from "./claim.mts";
import {
  numberOfBits,
  type Fields,
  type ClauseKey,
  type Row,
  type StringClause,
} from "./type-graph.mts";

/* What reaches the printers is the producer's, not this file's: a report shows
 * a claim that did not decode, and the lifter below names parts of a graph the
 * surface has no syntax for. So a read here narrows what arrived rather than
 * assuming a claim. */
function isObject(v: unknown): v is Record<string, unknown> {
  return v !== null && typeof v === "object";
}
/** A list of records where the producer sends one, the reading
 * `annotate-source.mts` makes of the same data: what arrives may not be one,
 * and a nullish element reaches the field read and throws there, as before. */
function isRecordList(v: unknown): v is Record<string, unknown>[] {
  return Array.isArray(v);
}
/** The atoms whose kind is all there is to them, read off `Atom` rather than
 * restated: the members whose only field is `a`. */
type BareKind<A> = A extends { a: infer K }
  ? keyof A extends "a"
    ? K
    : never
  : never;
const PRIMITIVE: BareKind<Atom>[] = [
  "null",
  "boolean",
  "string",
  "number",
  "bigint",
  "symbol",
  "undefined",
  "void",
];
const isPrimitive = (v: unknown): v is BareKind<Atom> =>
  PRIMITIVE.some((p) => p === v);
// A membership marker, not a table of names.
const LITERAL: Record<string, number> = {
  booleanlit: 1,
  stringlit: 1,
  numberlit: 1,
  numlit: 1,
};

/* ---------- printing ---------- */
/** Printing never fails; it records whether the text says the whole type. */
interface PrintState {
  printable: boolean;
}

function atomText(atom: unknown, state: PrintState): string {
  const text = bareAtomText(atom, state);
  if (!isObject(atom)) return text;
  const metadata: Record<string, unknown> = {};
  for (const key of ["call", "construct", "array"])
    if (key in atom && atom[key] !== "unknown") metadata[key] = atom[key];
  if (atom.indexes && Object.values(atom.indexes).some((v) => v !== "absent"))
    metadata.indexes = atom.indexes;
  if (atom.and !== undefined) metadata.and = atom.and;
  return Object.keys(metadata).length
    ? (atom.a === "function" ? "(" + text + ")" : text) +
        " @" +
        JSON.stringify(metadata)
    : text;
}
function bareAtomText(atom: unknown, state: PrintState): string {
  if (!isObject(atom)) {
    state.printable = false;
    return String(atom);
  }
  if (atom.unsupported === true) {
    state.printable = false;
    return "(unavailable)";
  }
  if (isPrimitive(atom.a) && Object.keys(atom).join() === "a") return atom.a;
  if (
    (atom.a === "array" || atom.a === "store") &&
    Array.isArray(atom.required) &&
    Array.isArray(atom.optional)
  ) {
    const required = atom.required.map((t) => typeText(t, state));
    const optional = atom.optional.map((t) => typeText(t, state) + "?");
    const rest = atom.rest === null ? null : typeText(atom.rest, state);
    const text =
      required.length === 0 && optional.length === 0 && rest !== null
        ? `${atom.readonly ? "ReadonlyArray" : "Array"}<${rest}>`
        : `${atom.readonly ? "readonly " : ""}[${[...required, ...optional, ...(rest === null ? [] : [`...Array<${rest}>`])].join(", ")}]`;
    return atom.a === "store" ? `Store<${text}>` : text;
  }
  if (atom.a === "param" && typeof atom.name === "string") return atom.name;
  if (
    atom.a === "alias" &&
    typeof atom.name === "string" &&
    Array.isArray(atom.args)
  )
    return (
      atom.name +
      "<" +
      atom.args.map((t: unknown) => typeText(t, state)).join(", ") +
      ">"
    );
  if (
    atom.a === "booleanlit" &&
    typeof atom.v === "string" &&
    ["true", "false"].includes(atom.v)
  )
    return atom.v;
  if (atom.a === "stringlit" && typeof atom.v === "string")
    return JSON.stringify(atom.v);
  if (
    (atom.a === "numberlit" || atom.a === "numlit") &&
    Number.isFinite(Number(atom.v))
  )
    return String(atom.v);
  if (atom.a === "record" && isRecordList(atom.fields)) {
    const index = isObject(atom.indexSignature) ? atom.indexSignature : null;
    const never = (t: unknown) =>
      isObject(t) &&
      t.top === false &&
      Array.isArray(t.atoms) &&
      t.atoms.length === 0;
    if (index && !never(index.write)) return JSON.stringify(atom);
    return (
      "{ " +
      [
        ...atom.fields.map((field) => {
          // A name the surface can write is written, anything else quoted,
          // and a symbol key is shown by its index.
          const key = field.name;
          const name =
            (typeof key === "string"
              ? /^[A-Za-z_$][\w$]*$/.test(key)
                ? key
                : JSON.stringify(key)
              : isObject(key) && typeof key.symbol === "number"
                ? `[symbol ${key.symbol}]`
                : JSON.stringify(key)) + (field.optional ? "?" : "");
          const read = typeText(field.read, state);
          const write = typeText(field.write, state);
          // A read type that differs from the write type is an assertion about
          // the cell's current contents, distinct from the storage invariant it
          // is written against. SOURCE-CLAIMS.md writes that `invariant =
          // (current)`; the two are not a read/write capability.
          return read === write
            ? name + ": " + read
            : name + ": " + write + " = (" + read + ")";
        }),
        ...(index
          ? [`readonly [key: string]: ${typeText(index.read, state)}`]
          : []),
      ].join(", ") +
      " }"
    );
  }
  if (atom.a === "callable")
    return (
      "(" + atomText(atom.function, state) + ") & " + atomText(atom.bag, state)
    );
  if (atom.a === "function" && Array.isArray(atom.params))
    return (
      "(" +
      [
        // A receiver-indifferent signature has no `this` to show.
        ...(isObject(atom.this) && atom.this.top === true
          ? []
          : ["this: " + typeText(atom.this, state)]),
        ...atom.params.map((p: unknown) => typeText(p, state)),
        ...(atom.rest === undefined
          ? []
          : ["...Array<" + typeText(atom.rest, state) + ">"]),
      ].join(", ") +
      ") => " +
      typeText(atom.result, state)
    );
  state.printable = false;
  return atom.a ? "«" + String(atom.a) + "»" : "«type»";
}

function typeText(type: unknown, state: PrintState): string {
  if (type === undefined || type === null) {
    state.printable = false;
    return "«missing»";
  }
  if (typeof type === "string") return type; // already a display string
  // Anything else is read for its fields, which a nonobject simply has none of.
  const shape: Record<string, unknown> = isObject(type) ? type : {};
  if (shape.unsupported === true) {
    state.printable = false;
    return "(unavailable)";
  }
  if (shape.top === true) return "unknown";
  const atoms: unknown[] | null = Array.isArray(shape.atoms)
    ? shape.atoms
    : null;
  if (!atoms) {
    state.printable = false;
    return "«type»";
  }
  if (!atoms.length) return "never";
  return atoms
    .map((atom: unknown) => {
      const text = atomText(atom, state);
      const kind = isObject(atom) ? atom.a : undefined;
      // Arrow results extend through a union, so an arrow that is itself a
      // union alternative needs grouping around the whole signature.
      return atoms.length > 1 && (kind === "function" || kind === "callable")
        ? "(" + text + ")"
        : text;
    })
    .join(" | ");
}

// `roundTrips` additionally checks that the self-contained text preserves every field.
function printType(type: unknown) {
  const state: PrintState = { printable: true };
  try {
    decodeClaimType(type);
  } catch {
    state.printable = false;
  }
  const text = typeText(type, state);
  return { text, printable: state.printable };
}

/* ---------- reading ---------- */
class TypeSyntaxError extends Error {}

function tokenize(text: string) {
  const tokens = [];
  const re =
    /\s+|\.\.\.|"(?:[^"\\]|\\.)*"|'(?:[^'\\]|\\.)*'|=>|[{}\[\](),:|?=&@<>]|[A-Za-z_$][\w$]*|-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?/g;
  let at = 0,
    m;
  while ((m = re.exec(text))) {
    if (m.index !== at)
      throw new TypeSyntaxError("unexpected character at " + at);
    at = m.index + m[0].length;
    if (!/^\s+$/.test(m[0])) tokens.push(m[0]);
  }
  if (at !== text.length)
    throw new TypeSyntaxError("unexpected character at " + at);
  return tokens;
}

function parseType(text: string): ClaimType {
  const tokens = tokenize(String(text));
  let i = 0;
  const peek = () => tokens[i];
  const take = (expected?: string) => {
    if (expected !== undefined && tokens[i] !== expected)
      throw new TypeSyntaxError(
        "expected " + expected + " but found " + (tokens[i] ?? "end of type"),
      );
    return tokens[i++];
  };

  const union = (): ClaimType => {
    if (peek() === "unknown") {
      take();
      return { top: true, atoms: [] };
    }
    if (peek() === "never") {
      take();
      return { top: false, atoms: [] };
    }
    const next = (): Atom => {
      let value = atom();
      while (peek() === "[") {
        take("[");
        take("]");
        value = {
          a: "array",
          required: [],
          optional: [],
          rest: { top: false, atoms: [value] },
          readonly: false,
        };
      }
      if (peek() === "@") {
        take("@");
        const start = i;
        take("{");
        let depth = 1;
        while (depth && i < tokens.length) {
          const token = take();
          if (token === "{") depth++;
          if (token === "}") depth--;
        }
        if (depth) throw new TypeSyntaxError("unterminated metadata");
        // The tokens are a balanced brace group, so this is an object or the
        // parse throws. Its keys are checked here; its values ride with the
        // atom into `decodeClaimType`, which is what validates them.
        const metadata: Record<string, unknown> = JSON.parse(
          tokens.slice(start, i).join(""),
        );
        const allowed =
          value.a === "record"
            ? ["call", "construct", "array", "indexes", "and"]
            : value.a === "function"
              ? ["construct", "array", "and"]
              : [];
        if (Object.keys(metadata).some((k) => !allowed.includes(k)))
          throw new TypeSyntaxError("unexpected type metadata");
        value = Object.assign(value, metadata);
      }
      return value;
    };
    const atoms = [next()];
    while (peek() === "|") {
      take("|");
      atoms.push(next());
    }
    return { top: false, atoms };
  };

  const atom = (): Atom => {
    const token = peek();
    if (token === undefined) throw new TypeSyntaxError("type expected");
    if (isPrimitive(token)) {
      take();
      return { a: token };
    }
    if (token === "readonly") {
      take();
      let inner = atom();
      while (peek() === "[") {
        take("[");
        take("]");
        inner = {
          a: "array",
          required: [],
          optional: [],
          rest: { top: false, atoms: [inner] },
          readonly: false,
        };
      }
      if (inner.a !== "array")
        throw new TypeSyntaxError("readonly needs an array or tuple");
      return { ...inner, readonly: true };
    }
    if (token === "[") {
      take("[");
      const required: ClaimType[] = [],
        optional: ClaimType[] = [];
      let rest: ClaimType | null = null;
      while (peek() !== "]") {
        if (rest !== null)
          throw new TypeSyntaxError("a tuple rest must be last");
        if (peek() === "...") {
          take();
          const t = union();
          const a = t.atoms[0];
          if (
            t.top ||
            t.atoms.length !== 1 ||
            a.a !== "array" ||
            a.required.length ||
            a.optional.length ||
            a.rest === null
          )
            throw new TypeSyntaxError(
              "a tuple rest needs an array element type",
            );
          rest = a.rest;
        } else {
          const t = union();
          if (peek() === "?") {
            take();
            optional.push(t);
          } else {
            if (optional.length)
              throw new TypeSyntaxError(
                "required position after optional position",
              );
            required.push(t);
          }
        }
        if (peek() !== ",") break;
        take();
      }
      take("]");
      return { a: "array", required, optional, rest, readonly: false };
    }
    if (token === "true" || token === "false")
      return { a: "booleanlit", v: take() };
    if (
      typeof token === "string" &&
      /^[A-Za-z_$][\w$]*$/.test(token) &&
      token !== "unknown" &&
      token !== "never"
    ) {
      if (tokens[i + 1] === "<") {
        const name = take();
        take("<");
        const args = peek() === ">" ? [] : [union()];
        while (peek() === ",") {
          take(",");
          args.push(union());
        }
        take(">");
        if (name === "Array" || name === "ReadonlyArray") {
          if (args.length !== 1)
            throw new TypeSyntaxError("an array needs one element type");
          return {
            a: "array",
            required: [],
            optional: [],
            rest: args[0],
            readonly: name === "ReadonlyArray",
          };
        }
        if (name === "Store") {
          const a = args[0]?.atoms[0];
          if (
            args.length !== 1 ||
            args[0].top ||
            args[0].atoms.length !== 1 ||
            a?.a !== "array"
          )
            throw new TypeSyntaxError("Store needs an array or tuple contract");
          return { ...a, a: "store" };
        }
        return { a: "alias", name, args };
      }
      return { a: "param", name: take() };
    }
    if (/^["']/.test(token)) {
      // A double-quoted token is already JSON; a single-quoted one becomes JSON
      // by swapping which quote is escaped.
      const raw = take();
      const json =
        raw[0] === '"'
          ? raw
          : '"' +
            raw.slice(1, -1).replace(/\\'/g, "'").replace(/"/g, '\\"') +
            '"';
      return { a: "stringlit", v: JSON.parse(json) };
    }
    if (/^-?\d/.test(token)) return { a: "numberlit", v: take() };
    if (token === "{") return record();
    if (token === "(") {
      // The matching ')' followed by '=>' identifies parameter parentheses.
      // Otherwise these parentheses group one union alternative.
      let end = i,
        depth = 0;
      do {
        if (tokens[end] === "(") depth++;
        if (tokens[end] === ")") depth--;
        end++;
      } while (end < tokens.length && depth > 0);
      if (tokens[end] === "&") {
        take("(");
        const fn = union();
        take(")");
        take("&");
        const bag = union();
        const f = fn.atoms[0],
          b = bag.atoms[0];
        if (
          fn.atoms.length !== 1 ||
          f.a !== "function" ||
          bag.atoms.length !== 1 ||
          b.a !== "record"
        )
          throw new TypeSyntaxError(
            "a callable combines one function and one object contract",
          );
        return { a: "callable", function: f, bag: b };
      }
      if (tokens[end] === "=>") return arrow();
      take("(");
      const grouped = union();
      take(")");
      if (peek() === "[") {
        take("[");
        take("]");
        return {
          a: "array",
          required: [],
          optional: [],
          rest: grouped,
          readonly: false,
        };
      }
      if (grouped.top || grouped.atoms.length !== 1)
        throw new TypeSyntaxError("expected a single grouped type alternative");
      return grouped.atoms[0];
    }
    throw new TypeSyntaxError("unexpected " + token);
  };

  const record = (): RecordAtom => {
    const base = {
      a: "record",
      indexes: { string: "absent", number: "absent", symbol: "absent" },
      call: "unknown",
      construct: "unknown",
      array: "unknown",
    };
    take("{");
    const fields: Field[] = [];
    let indexSignature: RecordAtom["indexSignature"];
    while (peek() !== "}") {
      if (peek() === "readonly" && tokens[i + 1] === "[") {
        if (indexSignature)
          throw new TypeSyntaxError("duplicate string index signature");
        take("readonly");
        take("[");
        take("key");
        take(":");
        take("string");
        take("]");
        take(":");
        indexSignature = { read: union(), write: { top: false, atoms: [] } };
        if (peek() === ",") take(",");
        else break;
        continue;
      }
      const rawName = take();
      // A quoted token is JSON, so it reads back as the string it spells.
      const name: string = rawName?.startsWith('"')
        ? JSON.parse(rawName)
        : rawName;
      if (!name || !/^(?:[A-Za-z_$][\w$]*|".*")$/.test(rawName))
        throw new TypeSyntaxError(
          "a field needs an identifier or a quoted name",
        );
      if (fields.some((field) => field.name === name))
        throw new TypeSyntaxError("field '" + name + "' appears twice");
      const optional = peek() === "?" ? (take("?"), true) : false;
      take(":");
      // `invariant = (current)` asserts contents against the storage invariant;
      // a bare type asserts both at once. Parentheses are the documented form
      // and are optional here, since a current predicate is a plain union.
      let read: ClaimType, write: ClaimType;
      write = union();
      if (peek() === "=") {
        take("=");
        const parenthesized = peek() === "(";
        if (parenthesized) take("(");
        read = union();
        if (parenthesized) take(")");
      } else read = structuredClone(write);
      fields.push({ name, optional, read, write });
      if (peek() === ",") take(",");
      else break;
    }
    take("}");
    // Bare records assert no call/construct/array restriction.
    return {
      ...base,
      a: "record",
      fields,
      ...(indexSignature ? { indexSignature } : {}),
    };
  };

  const arrow = (): FunctionAtom => {
    // Missing producer claims can be repaired with a new free signature. Its
    // syntax supplies domains/result; unknown modes assert no extra object
    // restrictions. Nondefault modes must be stated explicitly in the text.
    const base = {
      a: "function",
      construct: "unknown",
      array: "unknown",
    };
    take("(");
    const params: ClaimType[] = [];
    // `this: T` first states the receiver a call may pass; leaving it out
    // leaves the receiver unconstrained.
    let receiver: ClaimType = { top: true, atoms: [] };
    if (peek() === "this" && tokens[i + 1] === ":") {
      take("this");
      take(":");
      receiver = union();
      if (peek() === ",") take(",");
      else if (peek() !== ")")
        throw new TypeSyntaxError("expected , or ) after the receiver");
    }
    // `...Array<T>` last: any number of further actuals, each a `T`.
    let rest: ClaimType | undefined;
    while (peek() !== ")") {
      if (peek() === "...") {
        take("...");
        const t = union();
        const a = t.atoms[0];
        if (
          t.top ||
          t.atoms.length !== 1 ||
          a.a !== "array" ||
          a.required.length ||
          a.optional.length ||
          a.rest === null ||
          a.readonly
        )
          throw new TypeSyntaxError(
            "a rest parameter needs an Array<T> contract",
          );
        rest = a.rest;
        if (peek() !== ")")
          throw new TypeSyntaxError("a rest parameter must be the last one");
        break;
      }
      params.push(union());
      if (peek() === ",") take(",");
      else break;
    }
    take(")");
    take("=>");
    const result = union();
    return {
      ...base,
      a: "function",
      this: receiver,
      params,
      ...(rest === undefined ? {} : { rest }),
      result,
    };
  };

  const value = union();
  if (i !== tokens.length)
    throw new TypeSyntaxError("unexpected " + tokens[i] + " after the type");
  return decodeClaimType(value);
}

// Surface editing is offered only where the text says everything and reading it
// back returns the encoding it came from.
function roundTrips(type: unknown) {
  const printed = printType(type);
  if (!printed.printable) return false;
  try {
    const stable = (v: unknown): unknown =>
      Array.isArray(v)
        ? v.map(stable)
        : isObject(v)
          ? Object.fromEntries(
              Object.keys(v)
                .sort()
                .map((k) => [k, stable(v[k])]),
            )
          : v;
    return (
      JSON.stringify(stable(parseType(printed.text))) ===
      JSON.stringify(stable(type))
    );
  } catch (e) {
    return false;
  }
}

/* ---------- a whole claim, not just one type ---------- */
// Unavailable bindings have a marker which can be retained or replaced by
// a fresh type without pushing a whole environment into JSON.
const UNAVAILABLE = "(unavailable)";
/** The marker, which is not a claim: it says the producer decoded none. */
interface Undecoded {
  unsupported: true;
}
const undecoded = (type: unknown): type is Undecoded =>
  isObject(type) && type.unsupported === true;
/** An environment claim: named bindings, each holding the producer's own
 * encoding of a type, which this file need not be able to name. */
interface Binding {
  name: string;
  type: unknown;
}
const isBindingList = (v: unknown): v is Binding[] =>
  Array.isArray(v) && v.every((b) => isObject(b) && typeof b.name === "string");

function printClaimValue(kind: string, value: unknown) {
  if (kind === "expression")
    return undecoded(value)
      ? UNAVAILABLE
      : roundTrips(value)
        ? printType(value).text
        : null;
  if (!isBindingList(value) || !value.length) return null;
  if (!value.every((b) => undecoded(b.type) || roundTrips(b.type))) return null;
  return value
    .map(
      (b) =>
        b.name +
        ": " +
        (undecoded(b.type) ? UNAVAILABLE : printType(b.type).text),
    )
    .join(", ");
}

// Splits on commas outside braces and parentheses, so a binding's own type can
// contain either.
function splitBindings(text: string) {
  const parts = [];
  let depth = 0,
    start = 0;
  let quote = "",
    escaped = false;
  for (let i = 0; i < text.length; i++) {
    const c = text[i];
    if (quote) {
      if (escaped) escaped = false;
      else if (c === "\\") escaped = true;
      else if (c === quote) quote = "";
      continue;
    }
    if (c === '"' || c === "'") {
      quote = c;
      continue;
    }
    if (c === "{" || c === "(" || c === "[" || c === "<") depth++;
    else if (
      c === "}" ||
      c === ")" ||
      c === "]" ||
      (c === ">" && text[i - 1] !== "=")
    )
      depth--;
    else if (c === "," && depth === 0) {
      parts.push(text.slice(start, i));
      start = i + 1;
    }
  }
  parts.push(text.slice(start));
  return parts;
}

// The producer's encoding is wider than the calculus: it has numbers, strings
// and `any` because SKJS has them. A claim written in one of those cannot be
// checked at all, so saying so where it is typed beats letting it travel and
// come back later as a stopped verification. This names what is certainly
// outside; the verifier stays the authority on everything else.
const FRAGMENT = new Set(["null", "boolean", "booleanlit"]);
// Nothing found is falsy, which an atom stating no kind of its own also is:
// the scan stops at one either way, and says nothing about it.
function outsideFragment(type: unknown): string | undefined {
  if (undecoded(type)) return "";
  if (!isObject(type) || !isRecordList(type.atoms)) return "";
  if (type.top) return "any";
  for (const atom of type.atoms) {
    if (atom.a === "callable") {
      const found = outsideFragment({
        top: false,
        atoms: [atom.function, atom.bag],
      });
      if (found) return found;
      continue;
    }
    if (atom.a === "record") {
      for (const field of isRecordList(atom.fields) ? atom.fields : []) {
        const found =
          outsideFragment(field.read) || outsideFragment(field.write);
        if (found) return found;
      }
      if (isObject(atom.indexSignature)) {
        const found = outsideFragment(atom.indexSignature.read);
        if (found) return found;
      }
      continue;
    }
    if (atom.a === "function") {
      const params: unknown[] = Array.isArray(atom.params) ? atom.params : [];
      const rest = atom.rest === undefined ? [] : [atom.rest];
      for (const part of [atom.this, ...params, ...rest, atom.result]) {
        const found = outsideFragment(part);
        if (found) return found;
      }
      continue;
    }
    if (!atom.a) return undefined;
    if (typeof atom.a !== "string") return String(atom.a);
    if (!FRAGMENT.has(atom.a)) return atom.a;
  }
  return "";
}

// A claim value is a type, or for an environment a list of them.
function claimOutsideFragment(kind: string, value: unknown) {
  if (kind === "expression") return outsideFragment(value);
  for (const binding of isRecordList(value) ? value : []) {
    const found = outsideFragment(binding && binding.type);
    if (found) return found;
  }
  return "";
}

// An environment reads back as the bindings it was given, with the types the
// text states: what the surface does not name is the original's.
function readClaimValue(
  kind: "expression",
  text: string,
  current: unknown,
): ClaimType;
function readClaimValue(
  kind: "environment",
  text: string,
  current: unknown,
): Record<string, unknown>[];
function readClaimValue(
  kind: string,
  text: string,
  current: unknown,
): ClaimType | Record<string, unknown>[];
function readClaimValue(
  kind: string,
  text: string,
  current: unknown,
): ClaimType | Record<string, unknown>[] | Undecoded {
  if (kind === "expression") {
    if (String(text).trim() === UNAVAILABLE) {
      if (undecoded(current)) return current;
      throw new TypeSyntaxError("a claim cannot be made unavailable here");
    }
    return parseType(text);
  }
  // A name is whatever the binding states, which need not be text; the text
  // being read states one, so a binding naming anything else has none of it.
  const written = new Map<unknown, string>();
  for (const part of splitBindings(String(text))) {
    const at = part.indexOf(":");
    if (at < 0)
      throw new TypeSyntaxError(
        "each binding needs a name and a type: " + part.trim(),
      );
    const name = part.slice(0, at).trim();
    if (!name) throw new TypeSyntaxError("a binding needs a name");
    if (written.has(name))
      throw new TypeSyntaxError("binding '" + name + "' appears twice");
    written.set(name, part.slice(at + 1));
  }
  const bindings = isRecordList(current) ? current : [];
  const names: unknown[] = bindings.map((b) => b.name);
  for (const name of written.keys())
    if (!names.includes(name))
      throw new TypeSyntaxError(
        "'" + String(name) + "' is not a binding of this environment",
      );
  for (const name of names)
    if (!written.has(name))
      throw new TypeSyntaxError("binding '" + String(name) + "' is missing");
  return bindings.map((b) => {
    const value = (written.get(b.name) ?? "").trim();
    if (undecoded(b.type) && value === UNAVAILABLE) return b;
    return { ...b, type: parseType(value) };
  });
}

/* ---------- the normalized encoding ---------- */
// A candidate in the normalized encoding (SOURCE-CLAIMS.md) is a table of type
// rows and claims that index it. There is one editor, and it speaks the
// structural encoding above; so a normalized claim is lifted into that to be
// shown and lowered back on apply, interning into the document's own table
// whatever rows the edit needs, as the producer did on first use.

/** A type as the reader shows it, which is not a `ClaimType`: lifting stops
 * at a depth cut and names an intersection, or a clause it does not know, as
 * text where an atom belongs. The printers above take that in stride. */
interface Shown {
  top: boolean;
  atoms: unknown[];
}

// A cell row has the one-field source spelling, and the
// current-content assertion, where one is made, as that field's read side:
// `{ value: boolean = (true) }`, which POSITIVE-TYPES.md fixes as the source
// spelling of `x : ref(boolean) ∧ x ↦ true`.
/** A record contract's fields, as the claim language writes them. `current`
 * refines the read side of the fields it names; a field it does not name
 * reads at its own invariant. */
const cell = (
  types: unknown,
  contract: unknown,
  current: unknown,
  depth: number,
  views: unknown = [],
) => {
  const entries: unknown[] = Array.isArray(contract) ? contract : [];
  const asserted: unknown[] = Array.isArray(current) ? current : [];
  // A view field reads at its bound and accepts no write.
  const viewed: unknown[] = Array.isArray(views) ? views : [];
  const readonly = viewed.map((entry) => {
    const pair: unknown[] = Array.isArray(entry) ? entry : [];
    return {
      name: typeof pair[0] === "string" ? pair[0] : "",
      optional: false,
      read: liftType(types, pair[1], depth),
      write: { top: false, atoms: [] },
    };
  });
  return {
    a: "record",
    indexes: { string: "absent", number: "absent", symbol: "absent" },
    call: "unknown",
    construct: "unknown",
    array: "unknown",
    fields: [
      ...readonly,
      ...entries.map((entry) => {
        const pair: unknown[] = Array.isArray(entry) ? entry : [];
        const invariant = pair[1];
        const name = typeof pair[0] === "string" ? pair[0] : "";
        const now = asserted
          .map((a) => (Array.isArray(a) ? a : []))
          .find((a) => a[0] === name)?.[1];
        return {
          name,
          optional: false,
          read: liftType(types, now ?? invariant, depth),
          write: liftType(types, invariant, depth),
        };
      }),
    ],
  };
};

// An intersection of contracts has no surface form; it is shown as text and
// stays on the JSON path, like anything else the surface cannot name.
const shown = (atoms: unknown[]) =>
  atoms
    .map((atom) => printType({ top: false, atoms: [atom] }).text)
    .join(" & ");

// Every clause kind this lifter names. The graph arrives untyped, so the
// dispatch below cannot be narrowed; this table is checked instead, and a
// clause added to `Clause` without a case here does not compile.
const _handled = {
  nul: 1,
  bool: 1,
  undef: 1,
  num: 1,
  str: 1,
  top: 1,
  list: 1,
  boolLit: 1,
  numLit: 1,
  strLit: 1,
  refs: 1,
  dict: 1,
  arrs: 1,
  callable: 1,
  bigint: 1,
  symbol: 1,
} satisfies Record<StringClause | ClauseKey, 1>;
void _handled;

// A row, where the table has one under that label. Both arrive from the
// document, so neither is trusted to be there.
const rowAt = (types: unknown, label: unknown): unknown =>
  Array.isArray(types) &&
  (typeof label === "number" || typeof label === "string")
    ? Object.getOwnPropertyDescriptor(types, label)?.value
    : undefined;

function liftClause(types: unknown, clause: unknown, depth: number): unknown {
  if (clause === "nul") return { a: "null" };
  if (clause === "bool") return { a: "boolean" };
  if (clause === "undef") return { a: "undefined" };
  if (clause === "num") return { a: "number" };
  if (clause === "str") return { a: "string" };
  if (clause === "bigint") return { a: "bigint" };
  if (clause === "symbol") return { a: "symbol" };
  if (clause === "top") return "unknown";
  // A clause states one kind, under its own key. The table above is what
  // says these are all of them; here the key is only read.
  const body = (key: string): unknown =>
    isObject(clause) ? clause[key] : undefined;
  const boolLit = body("boolLit");
  if (boolLit)
    return {
      a: "booleanlit",
      v: String(isObject(boolLit) ? boolLit.value : undefined),
    };
  // The surface names the number, not the bit pattern that identifies it.
  const numLit = body("numLit");
  if (numLit)
    return {
      a: "numberlit",
      v: String(
        numberOfBits(String(isObject(numLit) ? numLit.bits : undefined)),
      ),
    };
  const strLit = body("strLit");
  if (strLit)
    return {
      a: "stringlit",
      v: String(isObject(strLit) ? strLit.value : undefined),
    };
  // The graph is finite but may be cyclic, so lifting stops rather than recursing.
  if (depth <= 0) return "…";
  const list = body("list");
  if (isObject(list) && isObject(list.first) && Array.isArray(list.rest)) {
    const t = list.first;
    if (
      list.rest.length ||
      !Array.isArray(t.required) ||
      !Array.isArray(t.optional)
    )
      return JSON.stringify(clause);
    return {
      a: "store",
      required: t.required.map((a) => liftType(types, a, depth - 1)),
      optional: t.optional.map((a) => liftType(types, a, depth - 1)),
      rest: t.rest === null ? null : liftType(types, t.rest, depth - 1),
      readonly: t.readonly,
    };
  }
  const refs = body("refs");
  if (refs) {
    const first = isObject(refs) ? refs.first : undefined;
    const rest: unknown[] =
      isObject(refs) && Array.isArray(refs.rest) ? refs.rest : [];
    const views = isObject(refs) ? refs.views : undefined;
    const cells = [first, ...rest].map((c, i) =>
      cell(types, c, null, depth - 1, i === 0 ? views : []),
    );
    if (cells.length === 1 && cells[0].fields.length === 1) {
      const f = cells[0].fields[0];
      const store =
        isObject(f.read) && Array.isArray(f.read.atoms)
          ? f.read.atoms[0]
          : undefined;
      if (
        f.name === "[]" &&
        isObject(store) &&
        store.a === "store" &&
        ((same(f.read, f.write) && store.readonly === false) ||
          (isObject(f.write) &&
            Array.isArray(f.write.atoms) &&
            f.write.atoms.length === 0 &&
            store.readonly === true))
      )
        return { ...store, a: "array" };
    }
    return cells.length === 1 ? cells[0] : shown(cells);
  }
  const dict = body("dict");
  if (isObject(dict)) {
    if (
      !Array.isArray(dict.rest) ||
      dict.rest.length ||
      !Array.isArray(dict.indexes) ||
      dict.indexes.length !== 1
    )
      return JSON.stringify(clause);
    const record = cell(types, dict.first, null, depth - 1, dict.views);
    return {
      ...record,
      indexSignature: {
        read: liftType(types, dict.indexes[0], depth - 1),
        write: { top: false, atoms: [] },
      },
    };
  }
  const callable = body("callable");
  if (callable) {
    const c: Record<string, unknown> = isObject(callable) ? callable : {};
    const rest: unknown[] = Array.isArray(c.rest) ? c.rest : [];
    const signatures = liftSignatures(types, c.arrows, c.variadic, depth);
    if (rest.length || signatures.length !== 1) return JSON.stringify(clause);
    return {
      a: "callable",
      function: signatures[0],
      bag: cell(types, c.first, null, depth - 1),
    };
  }
  const arrs = body("arrs");
  if (isObject(arrs)) {
    const arrows = liftSignatures(types, arrs.arrows, arrs.variadic, depth);
    if (arrows.length) return arrows.length === 1 ? arrows[0] : shown(arrows);
  }
  // Unknown clauses are shown as their encoding rather than guessed at.
  return JSON.stringify(clause);
}

/** A clause's call signatures as function atoms: its fixed arrows, then its
variadic ones, whose further actuals are at `rest`. */
function liftSignatures(
  types: unknown,
  fixed: unknown,
  variadic: unknown,
  depth: number,
): Record<string, unknown>[] {
  const atom = (
    receiver: unknown,
    domain: unknown,
    result: unknown,
    element?: unknown,
  ) => {
    const domains: unknown[] = Array.isArray(domain) ? domain : [];
    return {
      a: "function",
      construct: "unknown",
      array: "unknown",
      this: liftType(types, receiver, depth - 1),
      params: domains.map((D) => liftType(types, D, depth - 1)),
      ...(element === undefined
        ? {}
        : { rest: liftType(types, element, depth - 1) }),
      result: liftType(types, result, depth - 1),
    };
  };
  const arrows: unknown[] = Array.isArray(fixed) ? fixed : [];
  const sigs: unknown[] = Array.isArray(variadic) ? variadic : [];
  return [
    ...arrows.map((arrow) => {
      const [receiver, sig]: unknown[] = Array.isArray(arrow) ? arrow : [];
      const [domain, result]: unknown[] = Array.isArray(sig) ? sig : [];
      return atom(receiver, domain, result);
    }),
    ...sigs.map((sig) => {
      const [receiver, rest]: unknown[] = Array.isArray(sig) ? sig : [];
      const [domain, tail]: unknown[] = Array.isArray(rest) ? rest : [];
      const [element, result]: unknown[] = Array.isArray(tail) ? tail : [];
      return atom(receiver, domain, result, element);
    }),
  ];
}

function liftType(types: unknown, labels: unknown, depth: number): Shown {
  if (!Array.isArray(labels))
    return { top: false, atoms: ["(no type recorded)"] };
  if (
    labels.some((label) => {
      const row = rowAt(types, label);
      return Array.isArray(row) && row.includes("top");
    })
  )
    return { top: true, atoms: [] };
  // Recognize literals by their definitions, not their row numbers: native
  // request graphs need not use the source sidecar's primitive prefix.
  const literalLabel = (value: boolean): unknown =>
    labels.find((label: unknown) => {
      const row = rowAt(types, label);
      const clause =
        Array.isArray(row) && row.length === 1 ? row[0] : undefined;
      const boolLit = isObject(clause) ? clause.boolLit : undefined;
      return isObject(boolLit) && boolLit.value === value;
    });
  const trueLabel = literalLabel(true),
    falseLabel = literalLabel(false);
  const both = trueLabel !== undefined && falseLabel !== undefined;
  const atoms = labels.flatMap((label: unknown) => {
    if (both && label === falseLabel) return [];
    if (both && label === trueLabel) return [{ a: "boolean" }];
    const row = rowAt(types, label);
    if (!Array.isArray(row)) return ["type " + String(label)];
    return row.map((clause: unknown) => liftClause(types, clause, depth));
  });
  return { top: false, atoms };
}

// A point, lifted: its type, with the assertion about what the cell holds as
// the read side. Null where an assertion is made over a type that cannot
// carry one — only a single-contract cell holds anything.
function lift(
  types: unknown,
  labels: unknown,
  current: unknown = null,
  depth = 3,
): Shown | null {
  if (current == null) return liftType(types, labels, depth);
  const row =
    Array.isArray(labels) && labels.length === 1
      ? rowAt(types, labels[0])
      : null;
  const clause = Array.isArray(row) && row.length === 1 ? row[0] : null;
  const refs = isObject(clause) && isObject(clause.refs) ? clause.refs : null;
  if (!refs || (Array.isArray(refs.rest) ? refs.rest : []).length) return null;
  return { top: false, atoms: [cell(types, refs.first, current, depth - 1)] };
}

function intern(types: unknown, row: Row) {
  if (!Array.isArray(types))
    throw new TypeSyntaxError("this document has no type table to intern into");
  const key = JSON.stringify(row);
  const at = types.findIndex((r: unknown) => JSON.stringify(r) === key);
  if (at >= 0) return at;
  types.push(row);
  return types.length - 1;
}
const same = (a: unknown, b: unknown) =>
  JSON.stringify(a) === JSON.stringify(b);

// Every mode an atom states has to be one the graph can carry; a mode that is
// not a string is not one of them, which is what `includes` said before.
const stated = (mode: unknown, allowed: string[]) =>
  typeof mode === "string" && allowed.includes(mode);

function namedField(
  types: unknown,
  field: Record<string, unknown>,
  side: "read" | "write",
): [string, number[]] {
  if (typeof field.name !== "string")
    throw new TypeSyntaxError("a field needs a name");
  return [field.name, lowerType(types, field[side])];
}

function lowerAtom(types: unknown, atom: unknown): number[] {
  if (!isObject(atom)) throw new TypeSyntaxError("not a type: " + String(atom));
  for (const key of ["call", "construct", "array"])
    if (key in atom && !stated(atom[key], ["absent", "unknown"]))
      throw new TypeSyntaxError("unsupported object mode: " + key);
  if (
    isObject(atom.indexes) &&
    Object.values(atom.indexes).some((v) => v !== "absent" && v !== "synthetic")
  )
    throw new TypeSyntaxError("unsupported index requirement");
  if (atom.and !== undefined)
    throw new TypeSyntaxError(
      "enter simultaneous contracts in the native type graph",
    );
  if (atom.a === "number") return [intern(types, ["num"])];
  if (atom.a === "string") return [intern(types, ["str"])];
  if (atom.a === "bigint") return [intern(types, ["bigint"])];
  if (atom.a === "symbol") return [intern(types, ["symbol"])];
  if (atom.a === "stringlit" && typeof atom.v === "string")
    return [intern(types, [{ strLit: { value: atom.v } }])];
  if (
    atom.a === "numberlit" &&
    typeof atom.v === "string" &&
    Number.isFinite(Number(atom.v))
  ) {
    const buf = new ArrayBuffer(8),
      view = new DataView(buf);
    view.setFloat64(0, Number(atom.v) === 0 ? 0 : Number(atom.v));
    return [
      intern(
        types,
        Number(atom.v) === 0
          ? [
              { numLit: { bits: "0" } },
              { numLit: { bits: "9223372036854775808" } },
            ]
          : [{ numLit: { bits: view.getBigUint64(0).toString() } }],
      ),
    ];
  }
  if (atom.a === "void") return [intern(types, ["top"])];
  if (atom.a === "null") return [0];
  if (atom.a === "undefined") return [3];
  if (atom.a === "boolean") return [1, 2];
  if (atom.a === "booleanlit") return [String(atom.v) === "true" ? 1 : 2];
  if (atom.a === "array" || atom.a === "store") {
    if (
      !Array.isArray(atom.required) ||
      !Array.isArray(atom.optional) ||
      typeof atom.readonly !== "boolean"
    )
      throw new TypeSyntaxError("invalid array contract");
    const t = {
      required: atom.required.map((a) => lowerType(types, a)),
      optional: atom.optional.map((a) => lowerType(types, a)),
      rest: atom.rest === null ? null : lowerType(types, atom.rest),
      readonly: atom.readonly,
    };
    const store = intern(types, [{ list: { first: t, rest: [] } }]);
    if (atom.a === "store") return [store];
    const field: Fields = [["[]", [store]]];
    return [
      intern(types, [
        {
          refs: {
            first: atom.readonly ? [] : field,
            rest: [],
            views: atom.readonly ? field : [],
          },
        },
      ]),
    ];
  }
  if (atom.a === "record") {
    const fields = isRecordList(atom.fields) ? atom.fields : [];
    if (!fields.length && !atom.indexSignature)
      throw new TypeSyntaxError("a record with no field has no location");
    if (fields.some((f) => f.optional))
      throw new TypeSyntaxError("an optional field is not an invariant cell");
    // A field accepting no write is a readonly view of its read bound.
    const never = (t: unknown) =>
      isObject(t) &&
      t.top === false &&
      Array.isArray(t.atoms) &&
      t.atoms.length === 0;
    const invariant = fields.filter((f) => !never(f.write)),
      views = fields.filter((f) => never(f.write));
    if (invariant.some((f) => !same(f.read, f.write)))
      throw new TypeSyntaxError(
        "what a cell holds is asserted at the top of a claim, not inside a type",
      );

    const indexSignature = isObject(atom.indexSignature)
      ? atom.indexSignature
      : null;
    if (indexSignature && !never(indexSignature.write))
      throw new TypeSyntaxError(
        "only readonly string index signatures are supported",
      );
    const first = invariant.map((f) => namedField(types, f, "write"));
    const readViews = views.map((f) => namedField(types, f, "read"));
    return [
      intern(types, [
        indexSignature
          ? {
              dict: {
                first,
                rest: [],
                views: readViews,
                indexes: [lowerType(types, indexSignature.read)],
              },
            }
          : {
              refs: {
                first,
                rest: [],
                views: readViews,
              },
            },
      ]),
    ];
  }
  if (atom.a === "callable") {
    const f = isObject(atom.function) ? atom.function : undefined,
      bag = isObject(atom.bag) ? atom.bag : undefined;
    if (
      f?.and !== undefined ||
      bag?.and !== undefined ||
      [f?.construct, f?.array, bag?.call, bag?.construct, bag?.array].some(
        (v) => v !== undefined && !stated(v, ["unknown", "absent"]),
      ) ||
      Object.values(bag && isObject(bag.indexes) ? bag.indexes : {}).some(
        (v) => v !== "absent" && v !== "synthetic",
      )
    )
      throw new TypeSyntaxError("unsupported callable object requirement");
    const bagFields = bag && isRecordList(bag.fields) ? bag.fields : [];
    if (
      f?.a !== "function" ||
      bag?.a !== "record" ||
      !bagFields.length ||
      bagFields.some((fd) => fd.optional || !same(fd.read, fd.write))
    )
      throw new TypeSyntaxError(
        "a callable's properties must be required and invariant",
      );
    if (!Array.isArray(f.params))
      throw new TypeSyntaxError("a function needs a parameter list");
    const Rt = lowerType(types, f.this);
    const Ds = f.params.map((D: unknown) => lowerType(types, D));
    const R = lowerType(types, f.result);
    return [
      intern(types, [
        {
          callable: {
            first: bagFields.map((fd) => namedField(types, fd, "write")),
            rest: [],
            ...(f.rest === undefined
              ? { arrows: [[Rt, [Ds, R]]] }
              : {
                  arrows: [],
                  variadic: [[Rt, [Ds, [lowerType(types, f.rest), R]]]],
                }),
          },
        },
      ]),
    ];
  }
  if (atom.a === "function") {
    if (!Array.isArray(atom.params))
      throw new TypeSyntaxError("a function needs a parameter list");
    const receiver = lowerType(types, atom.this);
    const domains = atom.params.map((domain: unknown) =>
      lowerType(types, domain),
    );
    if (atom.rest !== undefined)
      return [
        intern(types, [
          {
            arrs: {
              arrows: [],
              variadic: [
                [
                  receiver,
                  [
                    domains,
                    [
                      lowerType(types, atom.rest),
                      lowerType(types, atom.result),
                    ],
                  ],
                ],
              ],
            },
          },
        ]),
      ];
    return [
      intern(types, [
        {
          arrs: {
            arrows: [[receiver, [domains, lowerType(types, atom.result)]]],
          },
        },
      ]),
    ];
  }
  throw new TypeSyntaxError(
    "'" +
      (atom.a ? String(atom.a) : "type") +
      "' is outside the checked fragment",
  );
}

function lowerType(types: unknown, type: unknown): number[] {
  if (!isObject(type) || !Array.isArray(type.atoms))
    throw new TypeSyntaxError("not a type");
  if (type.top) return [intern(types, ["top"])];
  const atoms: unknown[] = type.atoms;
  return Array.from(
    new Set<number>(atoms.flatMap((atom) => lowerAtom(types, atom))),
  ).sort((a, b) => a - b);
}

// A point, lowered: the encoding written directly is kept as written, so a
// label list comes back alone; a structural type comes back with the
// current-content assertion it makes, or `null` for none, as the format
// requires one or the other to be said.
function lower(
  types: unknown,
  type: unknown,
): { type: number[]; current?: [string, number[]][] | null } {
  if (Array.isArray(type)) return { type };
  const shape = isObject(type) ? type : null;
  const [first, ...more] =
    shape && Array.isArray(shape.atoms) ? shape.atoms : [];
  const atom =
    !more.length && isObject(first) && first.a === "record" ? first : null;
  const fields = atom && isRecordList(atom.fields) ? atom.fields : [];
  const narrowed = fields.filter(
    (f) =>
      !same(f.read, f.write) &&
      !(
        isObject(f.write) &&
        f.write.top === false &&
        Array.isArray(f.write.atoms) &&
        f.write.atoms.length === 0
      ),
  );
  if (shape && atom && narrowed.length) {
    const current: [string, number[]][] = narrowed.map((f) =>
      namedField(types, f, "read"),
    );
    const invariant = {
      ...shape,
      atoms: [
        { ...atom, fields: fields.map((f) => ({ ...f, read: f.write })) },
      ],
    };
    return { type: lowerType(types, invariant), current };
  }
  return { type: lowerType(types, type), current: null };
}

/* ---------- full printing, for snapshots ---------- */
// Every part of the encoding reaches the text, so two encodings that differ
// print differently: modes and index signatures, which the surface syntax
// leaves out, are listed after the atom when any is not `absent`, and a
// conjunction under `and` prints with `&`. This is for reading an export,
// never for reading text back.
function modesText(atom: Record<string, unknown>) {
  const parts = [];
  for (const key of ["call", "construct", "array"])
    if (key in atom && atom[key] !== "absent")
      parts.push(key + "=" + String(atom[key]));
  const indexes = atom.indexes;
  if (isObject(indexes))
    for (const kind of ["string", "number", "symbol"])
      if (kind in indexes && indexes[kind] !== "absent")
        parts.push(kind + "-index=" + String(indexes[kind]));
  return parts.length ? " [" + parts.join(" ") + "]" : "";
}
function fullAtomText(atom: unknown): string {
  if (!isObject(atom)) return String(atom);
  if (atom.unsupported === true) return "(unavailable)";
  let text;
  if (atom.a === "record" && isRecordList(atom.fields)) {
    const index = isObject(atom.indexSignature) ? atom.indexSignature : null;
    if (
      index &&
      !(
        isObject(index.write) &&
        index.write.top === false &&
        Array.isArray(index.write.atoms) &&
        index.write.atoms.length === 0
      )
    )
      return JSON.stringify(atom);
    text =
      "{ " +
      [
        ...atom.fields.map((field) => {
          const name =
            (typeof field.name === "string" &&
            /^[A-Za-z_$][\w$]*$/.test(field.name)
              ? field.name
              : JSON.stringify(field.name)) + (field.optional ? "?" : "");
          const read = fullTypeText(field.read);
          const write = fullTypeText(field.write);
          return read === write
            ? name + ": " + read
            : name + ": " + write + " = (" + read + ")";
        }),
        ...(index
          ? [`readonly [key: string]: ${fullTypeText(index.read)}`]
          : []),
      ].join(", ") +
      " }" +
      modesText(atom);
  } else if (atom.a === "callable")
    text = "(" + fullAtomText(atom.function) + ") & " + fullAtomText(atom.bag);
  else if (atom.a === "function" && Array.isArray(atom.params))
    text =
      "(" +
      [
        ...(isObject(atom.this) && atom.this.top === true
          ? []
          : ["this: " + fullTypeText(atom.this)]),
        ...atom.params.map((p: unknown) => fullTypeText(p)),
        ...(atom.rest === undefined
          ? []
          : ["...Array<" + fullTypeText(atom.rest) + ">"]),
      ].join(", ") +
      ") => " +
      fullTypeText(atom.result) +
      modesText(atom);
  else if (
    isPrimitive(atom.a) &&
    atom.a !== "void" &&
    Object.keys(atom).join() === "a"
  )
    text = atom.a;
  else if (atom.a === "param" && typeof atom.name === "string")
    text = atom.name;
  else if (
    atom.a === "alias" &&
    typeof atom.name === "string" &&
    Array.isArray(atom.args)
  )
    text =
      atom.name +
      "<" +
      atom.args.map((t: unknown) => fullTypeText(t)).join(", ") +
      ">";
  else if (typeof atom.a === "string" && LITERAL[atom.a] && "v" in atom)
    text = atom.a === "stringlit" ? JSON.stringify(atom.v) : String(atom.v);
  else {
    const { and, ...rest } = atom;
    text = JSON.stringify(rest);
  }
  if (Array.isArray(atom.and) && atom.and.length)
    text += atom.and
      .map((other: unknown) => " & " + fullAtomText(other))
      .join("");
  return text;
}
function fullTypeText(type: unknown): string {
  if (type === undefined || type === null) return "«missing»";
  if (typeof type === "string") return type;
  // As above: a nonobject has none of the fields read below.
  const shape: Record<string, unknown> = isObject(type) ? type : {};
  if (shape.unsupported === true) return "(unavailable)";
  if (shape.top === true) return "unknown";
  if (!Array.isArray(shape.atoms)) return JSON.stringify(type);
  const atoms: unknown[] = shape.atoms;
  if (!atoms.length) return "never";
  return atoms.map((atom) => fullAtomText(atom)).join(" | ");
}
function printFull(type: unknown) {
  return fullTypeText(type);
}

const surfaceTypes = {
  printType,
  printFull,
  parseType,
  roundTrips,
  printClaimValue,
  lift,
  lower,
  readClaimValue,
  claimOutsideFragment,
  TypeSyntaxError,
};

export default surfaceTypes;
