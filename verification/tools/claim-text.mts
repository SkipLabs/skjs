/* Surface text for the claim language declared in claim.mts, printed and read
 * back here so reports and the editor share one syntax. @ followed by a JSON
 * object states nondefault object modes and conjunction metadata explicitly.
 * The text always determines its type. */
import { decodeClaimType, type Atom, type ClaimType, type Field, type FunctionAtom, type RecordAtom } from "./claim.mts";
import { numberOfBits, type ClauseKey, type Row, type StringClause } from "./type-graph.mts";

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
type BareKind<A> = A extends { a: infer K } ? (keyof A extends "a" ? K : never) : never;
const PRIMITIVE: BareKind<Atom>[] = ["null", "boolean", "string", "number", "undefined"];
const isPrimitive = (v: unknown): v is BareKind<Atom> => PRIMITIVE.some((p) => p === v);
// A membership marker, not a table of names.
const LITERAL: Record<string, number> = { booleanlit: 1, stringlit: 1, numberlit: 1, numlit: 1 };

/* ---------- printing ---------- */
/** Printing never fails; it records whether the text says the whole type. */
interface PrintState { printable: boolean }

function atomText(atom: unknown, state: PrintState): string {
  const text = bareAtomText(atom, state);
  if (!isObject(atom)) return text;
  const metadata: Record<string, unknown> = {};
  for (const key of ["call", "construct", "array"])
    if (key in atom && atom[key] !== "unknown") metadata[key] = atom[key];
  if (atom.indexes && Object.values(atom.indexes).some(v => v !== "absent")) metadata.indexes = atom.indexes;
  if (atom.and !== undefined) metadata.and = atom.and;
  return Object.keys(metadata).length ? (atom.a === "function" ? "(" + text + ")" : text) + " @" + JSON.stringify(metadata) : text;
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
  if (isPrimitive(atom.a) && Object.keys(atom).join() === "a")
    return atom.a;
  if (atom.a === "param" && typeof atom.name === "string")
    return atom.name;
  if (atom.a === "alias" && typeof atom.name === "string" && Array.isArray(atom.args))
    return atom.name + "<" + atom.args.map((t: unknown) => typeText(t, state)).join(", ") + ">";
  if (atom.a === "booleanlit" && typeof atom.v === "string" && ["true", "false"].includes(atom.v))
    return atom.v;
  if (atom.a === "stringlit" && typeof atom.v === "string")
    return JSON.stringify(atom.v);
  if ((atom.a === "numberlit" || atom.a === "numlit") && Number.isFinite(Number(atom.v)))
    return String(atom.v);
  if (atom.a === "record" && isRecordList(atom.fields))
    return (
      "{ " +
      atom.fields
        .map((field) => {
          // A name the surface can write is written, anything else quoted. A
          // nonstring name prints the same either way: the regexp coerced it
          // before testing it, and the quoted form is that same text.
          const name = (typeof field.name === "string" && /^[A-Za-z_$][\w$]*$/.test(field.name) ? field.name : JSON.stringify(field.name)) + (field.optional ? "?" : "");
          const read = typeText(field.read, state);
          const write = typeText(field.write, state);
          // A read type that differs from the write type is an assertion about
          // the cell's current contents, distinct from the storage invariant it
          // is written against. SOURCE-CLAIMS.md writes that `invariant =
          // (current)`; the two are not a read/write capability.
          return read === write
            ? name + ": " + read
            : name + ": " + write + " = (" + read + ")";
        })
        .join(", ") +
      " }"
    );
  if (atom.a === "callable")
    return "(" + atomText(atom.function, state) + ") & " + atomText(atom.bag, state);
  if (atom.a === "function" && Array.isArray(atom.params))
    return (
      "(" +
      atom.params.map((p: unknown) => typeText(p, state)).join(", ") +
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
  const atoms: unknown[] | null = Array.isArray(shape.atoms) ? shape.atoms : null;
  if (!atoms) {
    state.printable = false;
    return "«type»";
  }
  if (!atoms.length) return "never";
  return atoms.map((atom: unknown) => {
    const text = atomText(atom, state);
    const kind = isObject(atom) ? atom.a : undefined;
    // Arrow results extend through a union, so an arrow that is itself a
    // union alternative needs grouping around the whole signature.
    return atoms.length > 1 && (kind === "function" || kind === "callable") ? "(" + text + ")" : text;
  }).join(" | ");
}

// `roundTrips` additionally checks that the self-contained text preserves every field.
  function printType(type: unknown) {
    const state: PrintState = { printable: true };
    try { decodeClaimType(type); } catch { state.printable = false; }
    const text = typeText(type, state);
    return { text, printable: state.printable };
  }

/* ---------- reading ---------- */
class TypeSyntaxError extends Error {}

function tokenize(text: string) {
  const tokens = [];
  const re =
    /\s+|"(?:[^"\\]|\\.)*"|'(?:[^'\\]|\\.)*'|=>|[{}\[\](),:|?=&@<>]|[A-Za-z_$][\w$]*|-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?/g;
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
        const metadata: Record<string, unknown> = JSON.parse(tokens.slice(start, i).join(""));
        const allowed = value.a === "record" ? ["call","construct","array","indexes","and"] :
          value.a === "function" ? ["construct","array","and"] : [];
        if (Object.keys(metadata).some(k => !allowed.includes(k))) throw new TypeSyntaxError("unexpected type metadata");
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
    if (isPrimitive(token)) { take(); return { a: token }; }
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
        const args = [union()];
        while (peek() === ",") {
          take(",");
          args.push(union());
        }
        take(">");
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
          : '"' + raw.slice(1, -1).replace(/\\'/g, "'").replace(/"/g, '\\"') + '"';
      return { a: "stringlit", v: JSON.parse(json) };
    }
    if (/^-?\d/.test(token)) return { a: "numberlit", v: take() };
    if (token === "{") return record();
    if (token === "(") {
      // The matching ')' followed by '=>' identifies parameter parentheses.
      // Otherwise these parentheses group one union alternative.
      let end = i, depth = 0;
      do {
        if (tokens[end] === "(") depth++;
        if (tokens[end] === ")") depth--;
        end++;
      } while (end < tokens.length && depth > 0);
      if (tokens[end] === "&") {
        take("(");
        const fn = union();
        take(")"); take("&");
        const bag = union();
        const f = fn.atoms[0], b = bag.atoms[0];
        if (fn.atoms.length !== 1 || f.a !== "function" || bag.atoms.length !== 1 || b.a !== "record")
          throw new TypeSyntaxError("a callable combines one function and one object contract");
        return {a: "callable", function: f, bag: b};
      }
      if (tokens[end] === "=>") return arrow();
      take("(");
      const grouped = union();
      take(")");
      if (grouped.top || grouped.atoms.length !== 1)
        throw new TypeSyntaxError("expected a single grouped type alternative");
      return grouped.atoms[0];
    }
    throw new TypeSyntaxError("unexpected " + token);
  };

  const record = (): RecordAtom => {
    const base = {
      a: "record", indexes: {string: "absent", number: "absent", symbol: "absent"},
      call: "unknown", construct: "unknown", array: "unknown",
    };
    take("{");
    const fields: Field[] = [];
    while (peek() !== "}") {
      const rawName = take();
      // A quoted token is JSON, so it reads back as the string it spells.
      const name: string = rawName?.startsWith('"') ? JSON.parse(rawName) : rawName;
      if (!name || !/^(?:[A-Za-z_$][\w$]*|".*")$/.test(rawName))
        throw new TypeSyntaxError("a field needs an identifier or a quoted name");
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
    return { ...base, a: "record", fields };
  };

  const arrow = (): FunctionAtom => {
    // Missing producer claims can be repaired with a new free signature. Its
    // syntax supplies domains/result; unknown modes assert no extra object
    // restrictions. Nondefault modes must be stated explicitly in the text.
    const base = {
      a: "function", construct: "unknown", array: "unknown",
    };
    take("(");
    const params: ClaimType[] = [];
    while (peek() !== ")") {
      params.push(union());
      if (peek() === ",") take(",");
      else break;
    }
    take(")");
    take("=>");
    const result = union();
    return { ...base, a: "function", params, result };
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
    const stable = (v: unknown): unknown => Array.isArray(v) ? v.map(stable) : isObject(v) ?
      Object.fromEntries(Object.keys(v).sort().map(k => [k,stable(v[k])])) : v;
    return JSON.stringify(stable(parseType(printed.text))) === JSON.stringify(stable(type));
  } catch (e) {
    return false;
  }
}


  /* ---------- a whole claim, not just one type ---------- */
  // Unavailable bindings have a marker which can be retained or replaced by
  // a fresh type without pushing a whole environment into JSON.
  const UNAVAILABLE = "(unavailable)";
  /** The marker, which is not a claim: it says the producer decoded none. */
  interface Undecoded { unsupported: true }
  const undecoded = (type: unknown): type is Undecoded => isObject(type) && type.unsupported === true;
  /** An environment claim: named bindings, each holding the producer's own
   * encoding of a type, which this file need not be able to name. */
  interface Binding { name: string; type: unknown }
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
    if (!value.every((b) => undecoded(b.type) || roundTrips(b.type)))
      return null;
    return value
      .map((b) => b.name + ": " + (undecoded(b.type) ? UNAVAILABLE : printType(b.type).text))
      .join(", ");
  }

  // Splits on commas outside braces and parentheses, so a binding's own type can
  // contain either.
  function splitBindings(text: string) {
    const parts = [];
    let depth = 0,
      start = 0;
    let quote = "", escaped = false;
    for (let i = 0; i < text.length; i++) {
      const c = text[i];
      if (quote) {
        if (escaped) escaped = false;
        else if (c === "\\") escaped = true;
        else if (c === quote) quote = "";
        continue;
      }
      if (c === '"' || c === "'") { quote = c; continue; }
      if (c === "{" || c === "(") depth++;
      else if (c === "}" || c === ")") depth--;
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
    if (!isObject(type) || !isRecordList(type.atoms))
      return "";
    if (type.top) return "any";
    for (const atom of type.atoms) {
      if (atom.a === "callable") {
        const found = outsideFragment({top: false, atoms: [atom.function, atom.bag]});
        if (found) return found;
        continue;
      }
      if (atom.a === "record") {
        for (const field of isRecordList(atom.fields) ? atom.fields : []) {
          const found =
            outsideFragment(field.read) || outsideFragment(field.write);
          if (found) return found;
        }
        continue;
      }
      if (atom.a === "function") {
        const params: unknown[] = Array.isArray(atom.params) ? atom.params : [];
        for (const part of [...params, atom.result]) {
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
  function readClaimValue(kind: "expression", text: string, current: unknown): ClaimType;
  function readClaimValue(kind: "environment", text: string, current: unknown): Record<string, unknown>[];
  function readClaimValue(kind: string, text: string, current: unknown): ClaimType | Record<string, unknown>[];
  function readClaimValue(kind: string, text: string, current: unknown): ClaimType | Record<string, unknown>[] | Undecoded {
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
        throw new TypeSyntaxError("each binding needs a name and a type: " + part.trim());
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
        throw new TypeSyntaxError("'" + String(name) + "' is not a binding of this environment");
    for (const name of names)
      if (!written.has(name)) throw new TypeSyntaxError("binding '" + String(name) + "' is missing");
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
  interface Shown { top: false; atoms: unknown[] }

  // A cell row has the one-field source spelling, and the
  // current-content assertion, where one is made, as that field's read side:
  // `{ value: boolean = (true) }`, which POSITIVE-TYPES.md fixes as the source
  // spelling of `x : ref(boolean) ∧ x ↦ true`.
  const cell = (types: unknown, invariant: unknown, current: unknown, depth: number) => ({
    a: "record",
    indexes: {string: "absent", number: "absent", symbol: "absent"},
    call: "unknown", construct: "unknown", array: "unknown",
    fields: [
      {
        name: "value",
        optional: false,
        read: liftType(types, current ?? invariant, depth),
        write: liftType(types, invariant, depth),
      },
    ],
  });

  // An intersection of contracts has no surface form; it is shown as text and
  // stays on the JSON path, like anything else the surface cannot name.
  const shown = (atoms: unknown[]) => atoms.map((atom) => printType({ top: false, atoms: [atom] }).text).join(" & ");

  // Every clause kind this lifter names. The graph arrives untyped, so the
  // dispatch below cannot be narrowed; this table is checked instead, and a
  // clause added to `Clause` without a case here does not compile.
  const _handled = {
    nul: 1, bool: 1, undef: 1, num: 1,
    boolLit: 1, numLit: 1, refs: 1, arrs: 1, callable: 1,
  } satisfies Record<StringClause | ClauseKey, 1>;
  void _handled;

  // A row, where the table has one under that label. Both arrive from the
  // document, so neither is trusted to be there.
  const rowAt = (types: unknown, label: unknown): unknown =>
    Array.isArray(types) && (typeof label === "number" || typeof label === "string")
      ? Object.getOwnPropertyDescriptor(types, label)?.value
      : undefined;

  function liftClause(types: unknown, clause: unknown, depth: number): unknown {
    if (clause === "nul") return { a: "null" };
    if (clause === "bool") return { a: "boolean" };
    if (clause === "undef") return { a: "undefined" };
    if (clause === "num") return { a: "number" };
    // A clause states one kind, under its own key. The table above is what
    // says these are all of them; here the key is only read.
    const body = (key: string): unknown => (isObject(clause) ? clause[key] : undefined);
    const boolLit = body("boolLit");
    if (boolLit) return { a: "booleanlit", v: String(isObject(boolLit) ? boolLit.value : undefined) };
    // The surface names the number, not the bit pattern that identifies it.
    const numLit = body("numLit");
    if (numLit)
      return { a: "numberlit", v: String(numberOfBits(String(isObject(numLit) ? numLit.bits : undefined))) };
    // The graph is finite but may be cyclic, so lifting stops rather than recursing.
    if (depth <= 0) return "…";
    const refs = body("refs");
    if (refs) {
      const first = isObject(refs) ? refs.first : undefined;
      const rest: unknown[] = isObject(refs) && Array.isArray(refs.rest) ? refs.rest : [];
      const cells = [first, ...rest].map((c) => cell(types, c, null, depth - 1));
      return cells.length === 1 ? cells[0] : shown(cells);
    }
    const callable = body("callable");
    if (callable) {
      const c: Record<string, unknown> = isObject(callable) ? callable : {};
      const rest: unknown[] = Array.isArray(c.rest) ? c.rest : [];
      const arrows: unknown[] = Array.isArray(c.arrows) ? c.arrows : [];
      if (rest.length || arrows.length !== 1) return JSON.stringify(clause);
      const [Ds,R]: unknown[] = Array.isArray(arrows[0]) ? arrows[0] : [];
      const domains: unknown[] = Array.isArray(Ds) ? Ds : [];
      return {a: "callable",
        function: {a: "function", construct: "unknown", array: "unknown", params: domains.map((D) => liftType(types,D,depth-1)),
          result: liftType(types,R,depth-1)},
        bag: cell(types,c.first,null,depth-1)};
    }
    const arrs = body("arrs");
    const stated: unknown[] = isObject(arrs) && Array.isArray(arrs.arrows) ? arrs.arrows : [];
    if (arrs && stated.length) {
      const arrows = stated.map((arrow) => {
        const [domain, result]: unknown[] = Array.isArray(arrow) ? arrow : [];
        const domains: unknown[] = Array.isArray(domain) ? domain : [];
        return {
          a: "function",
          construct: "unknown", array: "unknown",
          params: domains.map((D) => liftType(types, D, depth - 1)),
          result: liftType(types, result, depth - 1),
        };
      });
      return arrows.length === 1 ? arrows[0] : shown(arrows);
    }
    // Unknown clauses are shown as their encoding rather than guessed at.
    return JSON.stringify(clause);
  }

  function liftType(types: unknown, labels: unknown, depth: number): Shown {
    if (!Array.isArray(labels)) return { top: false, atoms: ["(no type recorded)"] };
    // Recognize literals by their definitions, not their row numbers: native
    // request graphs need not use the source sidecar's primitive prefix.
    const literalLabel = (value: boolean): unknown => labels.find((label: unknown) => {
      const row = rowAt(types, label);
      const clause = Array.isArray(row) && row.length === 1 ? row[0] : undefined;
      const boolLit = isObject(clause) ? clause.boolLit : undefined;
      return isObject(boolLit) && boolLit.value === value;
    });
    const trueLabel = literalLabel(true), falseLabel = literalLabel(false);
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
  function lift(types: unknown, labels: unknown, current: unknown = null, depth = 3): Shown | null {
    if (current == null) return liftType(types, labels, depth);
    const row = Array.isArray(labels) && labels.length === 1 ? rowAt(types, labels[0]) : null;
    const clause = Array.isArray(row) && row.length === 1 ? row[0] : null;
    const refs = isObject(clause) && isObject(clause.refs) ? clause.refs : null;
    if (!refs || (Array.isArray(refs.rest) ? refs.rest : []).length) return null;
    return { top: false, atoms: [cell(types, refs.first, current, depth - 1)] };
  }

  function intern(types: unknown, row: Row) {
    if (!Array.isArray(types)) throw new TypeSyntaxError("this document has no type table to intern into");
    const key = JSON.stringify(row);
    const at = types.findIndex((r: unknown) => JSON.stringify(r) === key);
    if (at >= 0) return at;
    types.push(row);
    return types.length - 1;
  }
  const same = (a: unknown, b: unknown) => JSON.stringify(a) === JSON.stringify(b);

  // Every mode an atom states has to be one the graph can carry; a mode that is
  // not a string is not one of them, which is what `includes` said before.
  const stated = (mode: unknown, allowed: string[]) => typeof mode === "string" && allowed.includes(mode);

  function lowerAtom(types: unknown, atom: unknown): number[] {
    if (!isObject(atom)) throw new TypeSyntaxError("not a type: " + String(atom));
    for (const key of ["call","construct","array"])
      if (key in atom && !stated(atom[key], ["absent","unknown"])) throw new TypeSyntaxError("unsupported object mode: " + key);
    if (isObject(atom.indexes) && Object.values(atom.indexes).some(v => v !== "absent" && v !== "synthetic"))
      throw new TypeSyntaxError("unsupported index requirement");
    if (atom.and !== undefined) throw new TypeSyntaxError("enter simultaneous contracts in the native type graph");
    if (atom.a === "null") return [0];
    if (atom.a === "undefined") return [3];
    if (atom.a === "boolean") return [1, 2];
    if (atom.a === "booleanlit") return [String(atom.v) === "true" ? 1 : 2];
    if (atom.a === "record") {
      const [field, ...more] = isRecordList(atom.fields) ? atom.fields : [];
      if (!field || more.length || field.name !== "value" || field.optional)
        throw new TypeSyntaxError("a cell is an object with the one field 'value'");
      if (!same(field.read, field.write))
        throw new TypeSyntaxError("what a cell holds is asserted at the top of a claim, not inside a type");
      return [intern(types, [{ refs: { first: lowerType(types, field.write), rest: [] } }])];
    }
    if (atom.a === "callable") {
      const f = isObject(atom.function) ? atom.function : undefined, bag = isObject(atom.bag) ? atom.bag : undefined;
      if (f?.and !== undefined || bag?.and !== undefined ||
          [f?.construct,f?.array,bag?.call,bag?.construct,bag?.array].some(v => v !== undefined && !stated(v, ["unknown","absent"])) ||
          Object.values(bag && isObject(bag.indexes) ? bag.indexes : {}).some(v => v !== "absent" && v !== "synthetic"))
        throw new TypeSyntaxError("unsupported callable object requirement");
      const [field, ...more] = bag && isRecordList(bag.fields) ? bag.fields : [];
      if (f?.a !== "function" || bag?.a !== "record" || !field || more.length ||
          field.name !== "value" || field.optional || !same(field.read, field.write))
        throw new TypeSyntaxError("a callable field requires one invariant value property");
      if (!Array.isArray(f.params)) throw new TypeSyntaxError("a function needs a parameter list");
      return [intern(types, [{callable: {first: lowerType(types,field.write), rest: [],
        arrows: [[f.params.map((D: unknown) => lowerType(types,D)), lowerType(types,f.result)]]}}])];
    }
    if (atom.a === "function") {
      if (!Array.isArray(atom.params)) throw new TypeSyntaxError("a function needs a parameter list");
      const domains = atom.params.map((domain: unknown) => lowerType(types, domain));
      return [intern(types, [{ arrs: { arrows: [[domains, lowerType(types, atom.result)]] } }])];
    }
    throw new TypeSyntaxError("'" + (atom.a ? String(atom.a) : "type") + "' is outside the checked fragment");
  }

  function lowerType(types: unknown, type: unknown): number[] {
    if (!isObject(type) || !Array.isArray(type.atoms)) throw new TypeSyntaxError("not a type");
    if (type.top) throw new TypeSyntaxError("'unknown' is outside the checked fragment");
    const atoms: unknown[] = type.atoms;
    return Array.from(new Set<number>(atoms.flatMap((atom) => lowerAtom(types, atom)))).sort((a, b) => a - b);
  }

  // A point, lowered: the encoding written directly is kept as written, so a
  // label list comes back alone; a structural type comes back with the
  // current-content assertion it makes, or `null` for none, as the format
  // requires one or the other to be said.
  function lower(types: unknown, type: unknown): { type: number[]; current?: number[] | null } {
    if (Array.isArray(type)) return { type };
    const shape = isObject(type) ? type : null;
    const [first, ...more] = shape && Array.isArray(shape.atoms) ? shape.atoms : [];
    const atom = !more.length && isObject(first) && first.a === "record" ? first : null;
    const fields: unknown[] = atom && Array.isArray(atom.fields) ? atom.fields : [];
    const field = atom && isObject(fields[0]) ? fields[0] : null;
    if (shape && atom && field && fields.length === 1 && field.name === "value" && !same(field.read, field.write)) {
      const current = lowerType(types, field.read);
      if (current.some((l) => l > 3)) throw new TypeSyntaxError("a cell holds null, true, false or undefined");
      const invariant = { ...shape, atoms: [{ ...atom, fields: [{ ...field, read: field.write }] }] };
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
      if (key in atom && atom[key] !== "absent") parts.push(key + "=" + String(atom[key]));
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
    if (atom.a === "record" && isRecordList(atom.fields))
      text =
        "{ " +
        atom.fields
          .map((field) => {
            const name = (typeof field.name === "string" && /^[A-Za-z_$][\w$]*$/.test(field.name) ? field.name : JSON.stringify(field.name)) + (field.optional ? "?" : "");
            const read = fullTypeText(field.read);
            const write = fullTypeText(field.write);
            return read === write
              ? name + ": " + read
              : name + ": " + write + " = (" + read + ")";
          })
          .join(", ") +
        " }" +
        modesText(atom);
    else if (atom.a === "callable")
      text = "(" + fullAtomText(atom.function) + ") & " + fullAtomText(atom.bag);
    else if (atom.a === "function" && Array.isArray(atom.params))
      text =
        "(" +
        atom.params.map((p: unknown) => fullTypeText(p)).join(", ") +
        ") => " +
        fullTypeText(atom.result) +
        modesText(atom);
    else if (isPrimitive(atom.a) && Object.keys(atom).join() === "a")
      text = atom.a;
    else if (atom.a === "param" && typeof atom.name === "string")
      text = atom.name;
    else if (atom.a === "alias" && typeof atom.name === "string" && Array.isArray(atom.args))
      text = atom.name + "<" + atom.args.map((t: unknown) => fullTypeText(t)).join(", ") + ">";
    else if (typeof atom.a === "string" && LITERAL[atom.a] && "v" in atom)
      text = atom.a === "stringlit" ? JSON.stringify(atom.v) : String(atom.v);
    else {
      const { and, ...rest } = atom;
      text = JSON.stringify(rest);
    }
    if (Array.isArray(atom.and) && atom.and.length)
      text += atom.and.map((other: unknown) => " & " + fullAtomText(other)).join("");
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
