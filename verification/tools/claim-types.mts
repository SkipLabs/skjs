/* Claim types in surface syntax, shared by the report writer and the reader.
 *
 * The producer's encoding is authoritative and unreadable: a cell holding a
 * boolean is three hundred bytes of JSON. This prints it as `{ value: boolean }`
 * and reads that back, so claims can be read and edited in the syntax they were
 * written in.
 *
 * The text is a view, not an encoding. Surface syntax does not show everything
 * a claim carries — index signatures, call and construct shapes, per-field
 * optionality, and whatever a future producer adds — so reading it back needs
 * the claim it came from: what the text names is replaced, and what it does not
 * name is taken from that original rather than invented here. `printable` says
 * the text names the type faithfully, not that it is self-contained. A shape
 * this module cannot name is not printed at all, and stays on the JSON path.
 *
 * The manifest keeps the producer's encoding; comments and panels show this.
 */

// One namespace, and nothing else in the page's shared scope: these files are
// plain scripts, and a bare `typeText` here would silently replace another's.
const surfaceTypes = (() => {
const PRIMITIVE = ["null", "boolean", "string", "number", "undefined"];
// A membership marker, not a table of names.
const LITERAL: Record<string, number> = { booleanlit: 1, stringlit: 1, numberlit: 1, numlit: 1 };

/* ---------- printing ---------- */
function atomText(atom: any, state: any) {
  if (!atom || typeof atom !== "object") {
    state.printable = false;
    return String(atom);
  }
  if (atom.unsupported === true) {
    state.printable = false;
    return "(unavailable)";
  }
  if (PRIMITIVE.includes(atom.a) && Object.keys(atom).join() === "a")
    return atom.a;
  if (atom.a === "booleanlit" && ["true", "false"].includes(atom.v))
    return atom.v;
  if (atom.a === "stringlit" && typeof atom.v === "string")
    return JSON.stringify(atom.v);
  if ((atom.a === "numberlit" || atom.a === "numlit") && Number.isFinite(Number(atom.v)))
    return String(atom.v);
  if (atom.a === "record" && Array.isArray(atom.fields))
    return (
      "{ " +
      atom.fields
        .map((field: any) => {
          const name = field.name + (field.optional ? "?" : "");
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
  if (atom.a === "function" && Array.isArray(atom.params))
    return (
      "(" +
      atom.params.map((p: any) => typeText(p, state)).join(", ") +
      ") => " +
      typeText(atom.result, state)
    );
  state.printable = false;
  return atom.a ? "«" + atom.a + "»" : "«type»";
}

function typeText(type: any, state: any) {
  if (type === undefined || type === null) {
    state.printable = false;
    return "«missing»";
  }
  if (typeof type === "string") return type; // already a display string
  if (type.unsupported === true) {
    state.printable = false;
    return "(unavailable)";
  }
  if (type.top === true) return "unknown";
  const atoms = Array.isArray(type.atoms) ? type.atoms : null;
  if (!atoms) {
    state.printable = false;
    return "«type»";
  }
  if (!atoms.length) return "never";
  return atoms.map((atom: any) => {
    const text = atomText(atom, state);
    // Arrow results extend through a union, so an arrow that is itself a
    // union alternative needs grouping around the whole signature.
    return atoms.length > 1 && atom?.a === "function" ? "(" + text + ")" : text;
  }).join(" | ");
}

// `printable` says the text names this type in surface syntax. It does not say
  // the text alone determines the encoding: reading it back uses the original,
  // because index signatures, callable shapes and optionality are not shown.
  function printType(type: any) {
    const state = { printable: true };
    const text = typeText(type, state);
    return { text, printable: state.printable };
  }

/* ---------- reading ---------- */
class TypeSyntaxError extends Error {}

function tokenize(text: string) {
  const tokens = [];
  const re =
    /\s+|"(?:[^"\\]|\\.)*"|'(?:[^'\\]|\\.)*'|=>|[{}(),:|?=]|[A-Za-z_$][\w$]*|-?\d+(?:\.\d+)?/g;
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

function parseType(text: string, template: any) {
  const tokens = tokenize(String(text));
  let i = 0;
  const peek = () => tokens[i];
  const take = (expected?: any) => {
    if (expected !== undefined && tokens[i] !== expected)
      throw new TypeSyntaxError(
        "expected " + expected + " but found " + (tokens[i] ?? "end of type"),
      );
    return tokens[i++];
  };
  // Templates supply what the surface does not name. A union is matched by atom
  // kind, consuming each occurrence once within that union. This retains each
  // alternative's hidden structure even when several have the same kind.
  const templateAtom = (from: any, kind: string) =>
    (from && Array.isArray(from.atoms) ? from.atoms : []).find((a: any) => a.a === kind) ||
    null;

  const union = (from: any): any => {
    if (peek() === "unknown") {
      take();
      return { top: true, atoms: [] };
    }
    if (peek() === "never") {
      take();
      return { top: false, atoms: [] };
    }
    const remaining = [...(from?.atoms || [])];
    const next = () => {
      const value = atom({...from,atoms:remaining});
      const index = remaining.findIndex((a: any) => a.a === value.a);
      if (index >= 0) remaining.splice(index,1);
      return value;
    };
    const atoms = [next()];
    while (peek() === "|") {
      take("|");
      atoms.push(next());
    }
    return { top: false, atoms };
  };

  const atom = (from: any) => {
    const token = peek();
    if (token === undefined) throw new TypeSyntaxError("type expected");
    if (PRIMITIVE.includes(token)) return { a: take() };
    if (token === "true" || token === "false")
      return { a: "booleanlit", v: take() };
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
    if (token === "{") return record(from);
    if (token === "(") {
      // The matching ')' followed by '=>' identifies parameter parentheses.
      // Otherwise these parentheses group one union alternative.
      let end = i, depth = 0;
      do {
        if (tokens[end] === "(") depth++;
        if (tokens[end] === ")") depth--;
        end++;
      } while (end < tokens.length && depth > 0);
      if (tokens[end] === "=>") return arrow(from);
      take("(");
      const grouped = union(from);
      take(")");
      if (grouped.top || grouped.atoms.length !== 1)
        throw new TypeSyntaxError("expected a single grouped type alternative");
      return grouped.atoms[0];
    }
    throw new TypeSyntaxError("unexpected " + token);
  };

  const record = (from: any) => {
    const base = templateAtom(from, "record");
    if (!base)
      throw new TypeSyntaxError(
        "an object type can only be edited from an existing object type",
      );
    take("{");
    const fields = [];
    while (peek() !== "}") {
      const name = take();
      const optional = peek() === "?" ? (take("?"), true) : false;
      take(":");
      // A name the original does not have would take another field's hidden
      // structure. Dropping a field is expressible; inventing one is not.
      const original = (base.fields || []).find((f: any) => f.name === name);
      if (!original)
        throw new TypeSyntaxError(
          "this object type has no field '" + name + "'",
        );
      // `invariant = (current)` asserts contents against the storage invariant;
      // a bare type asserts both at once. Parentheses are the documented form
      // and are optional here, since a current predicate is a plain union.
      let read, write;
      write = union(original.write);
      if (peek() === "=") {
        take("=");
        const parenthesized = peek() === "(";
        if (parenthesized) take("(");
        read = union(original.read);
        if (parenthesized) take(")");
      } else read = structuredClone(write);
      fields.push({ ...original, name, optional, read, write });
      if (peek() === ",") take(",");
      else break;
    }
    take("}");
    // Everything the surface does not name — indexes, call, construct, array —
    // is the original's, not this reader's invention.
    return { ...base, a: "record", fields };
  };

  const arrow = (from: any) => {
    const base = templateAtom(from, "function");
    if (!base)
      throw new TypeSyntaxError(
        "a function type can only be edited from an existing function type",
      );
    take("(");
    const params = [];
    while (peek() !== ")") {
      params.push(union((base.params || [])[params.length]));
      if (peek() === ",") take(",");
      else break;
    }
    take(")");
    take("=>");
    const result = union(base.result);
    return { ...base, a: "function", params, result };
  };

  const value = union(template);
  if (i !== tokens.length)
    throw new TypeSyntaxError("unexpected " + tokens[i] + " after the type");
  return value;
}

// Surface editing is offered only where the text says everything and reading it
// back returns the encoding it came from.
function roundTrips(type: any) {
  const printed = printType(type);
  if (!printed.printable) return false;
  try {
    return JSON.stringify(parseType(printed.text, type)) === JSON.stringify(type);
  } catch (e) {
    return false;
  }
}

// One namespace either way: a module in the tests, a single global in the page,
// so no script has to declare a name another script already owns.

  /* ---------- a whole claim, not just one type ---------- */
  // A binding the producer could not decode has no surface form and no claim to
  // edit. It is carried through as it is, so one such binding does not push a
  // whole environment back into JSON.
  const UNAVAILABLE = "(unavailable)";
  const undecoded = (type: any) => Boolean(type) && type.unsupported === true;

  function printClaimValue(kind: string, value: any) {
    if (kind === "expression")
      return undecoded(value)
        ? UNAVAILABLE
        : roundTrips(value)
          ? printType(value).text
          : null;
    if (!Array.isArray(value) || !value.length) return null;
    if (!value.every((b) => b && typeof b.name === "string" && (undecoded(b.type) || roundTrips(b.type))))
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
    for (let i = 0; i < text.length; i++) {
      const c = text[i];
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
  function outsideFragment(type: any): any {
    if (undecoded(type)) return "";
    if (!type || typeof type !== "object" || !Array.isArray(type.atoms))
      return "";
    if (type.top) return "any";
    for (const atom of type.atoms) {
      if (atom.a === "record") {
        for (const field of atom.fields || []) {
          const found =
            outsideFragment(field.read) || outsideFragment(field.write);
          if (found) return found;
        }
        continue;
      }
      if (atom.a === "function") {
        for (const part of [...(atom.params || []), atom.result]) {
          const found: any = outsideFragment(part);
          if (found) return found;
        }
        continue;
      }
      if (!FRAGMENT.has(atom.a)) return atom.a;
    }
    return "";
  }

  // A claim value is a type, or for an environment a list of them.
  function claimOutsideFragment(kind: string, value: any) {
    if (kind === "expression") return outsideFragment(value);
    for (const binding of value || []) {
      const found: any = outsideFragment(binding && binding.type);
      if (found) return found;
    }
    return "";
  }

  function readClaimValue(kind: string, text: string, current: any) {
    if (kind === "expression") {
      if (String(text).trim() === UNAVAILABLE) {
        if (undecoded(current)) return current;
        throw new TypeSyntaxError("a claim cannot be made unavailable here");
      }
      return parseType(text, current);
    }
    const written = new Map();
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
    const names = (current || []).map((b: any) => b.name);
    for (const name of written.keys())
      if (!names.includes(name))
        throw new TypeSyntaxError("'" + name + "' is not a binding of this environment");
    for (const name of names)
      if (!written.has(name)) throw new TypeSyntaxError("binding '" + name + "' is missing");
    return current.map((b: any) => {
      const value = written.get(b.name).trim();
      if (undecoded(b.type)) {
        // Its type was never decoded, so there is nothing here to edit against.
        if (value !== UNAVAILABLE)
          throw new TypeSyntaxError(
            "the producer could not decode '" +
              b.name +
              "'; give it a type in the producer encoding, not here",
          );
        return b;
      }
      return { ...b, type: parseType(value, b.type) };
    });
  }

  /* ---------- the normalized encoding ---------- */
  // A candidate in the normalized encoding (SOURCE-CLAIMS.md) is a table of type
  // rows and claims that index it. There is one editor, and it speaks the
  // structural encoding above; so a normalized claim is lifted into that to be
  // shown and lowered back on apply, interning into the document's own table
  // whatever rows the edit needs, as the producer did on first use.

  // A cell row is read as the one-field object the source declared, and the
  // current-content assertion, where one is made, as that field's read side:
  // `{ value: boolean = (true) }`, which POSITIVE-TYPES.md fixes as the source
  // spelling of `x : ref(boolean) ∧ x ↦ true`.
  const cell = (types: any, invariant: any, current: any, depth: number) => ({
    a: "record",
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
  const shown = (atoms: any[]) => atoms.map((atom) => printType({ top: false, atoms: [atom] }).text).join(" & ");

  function liftClause(types: any, clause: any, depth: number): any {
    if (clause === "nul") return { a: "null" };
    if (clause === "bool") return { a: "boolean" };
    if (clause === "undef") return { a: "undefined" };
    if (clause && clause.boolLit) return { a: "booleanlit", v: String(clause.boolLit.value) };
    // The graph is finite but may be cyclic, so lifting stops rather than recursing.
    if (depth <= 0) return "…";
    if (clause && clause.refs) {
      const cells = [clause.refs.first, ...(clause.refs.rest || [])].map((c) => cell(types, c, null, depth - 1));
      return cells.length === 1 ? cells[0] : shown(cells);
    }
    if (clause && clause.arrs && (clause.arrs.arrows || []).length) {
      const arrows = clause.arrs.arrows.map(([domain, result]: [any, any]) => ({
        a: "function",
        params: domain.map((D: number[]) => liftType(types, D, depth - 1)),
        result: liftType(types, result, depth - 1),
      }));
      return arrows.length === 1 ? arrows[0] : shown(arrows);
    }
    // Unknown clauses are shown as their encoding rather than guessed at.
    return JSON.stringify(clause);
  }

  function liftType(types: any, labels: any, depth: number): any {
    if (!Array.isArray(labels)) return { top: false, atoms: ["(no type recorded)"] };
    // Rows 1 and 2 are the fixed literals a source `boolean` is lowered to, so
    // the pair is read back as the source wrote it.
    const both = labels.includes(1) && labels.includes(2);
    const atoms = labels.flatMap((label) => {
      if (both && label === 2) return [];
      if (both && label === 1) return [{ a: "boolean" }];
      const row = types?.[label];
      if (!Array.isArray(row)) return ["type " + label];
      return row.map((clause) => liftClause(types, clause, depth));
    });
    return { top: false, atoms };
  }

  // A point, lifted: its type, with the assertion about what the cell holds as
  // the read side. Null where an assertion is made over a type that cannot
  // carry one — only a single-contract cell holds anything.
  function lift(types: any, labels: any, current: any = null, depth = 3) {
    if (current == null) return liftType(types, labels, depth);
    const row = Array.isArray(labels) && labels.length === 1 ? types?.[labels[0]] : null;
    const refs = Array.isArray(row) && row.length === 1 ? (row[0] as any)?.refs : null;
    if (!refs || (refs.rest || []).length) return null;
    return { top: false, atoms: [cell(types, refs.first, current, depth - 1)] };
  }

  function intern(types: any, row: any) {
    if (!Array.isArray(types)) throw new TypeSyntaxError("this document has no type table to intern into");
    const key = JSON.stringify(row);
    const at = types.findIndex((r: any) => JSON.stringify(r) === key);
    if (at >= 0) return at;
    types.push(row);
    return types.length - 1;
  }
  const same = (a: any, b: any) => JSON.stringify(a) === JSON.stringify(b);

  function lowerAtom(types: any, atom: any): number[] {
    if (!atom || typeof atom !== "object") throw new TypeSyntaxError("not a type: " + String(atom));
    if (atom.a === "null") return [0];
    if (atom.a === "undefined") return [3];
    if (atom.a === "boolean") return [1, 2];
    if (atom.a === "booleanlit") return [String(atom.v) === "true" ? 1 : 2];
    if (atom.a === "record") {
      const [field, ...more] = atom.fields || [];
      if (!field || more.length || field.name !== "value" || field.optional)
        throw new TypeSyntaxError("a cell is an object with the one field 'value'");
      if (!same(field.read, field.write))
        throw new TypeSyntaxError("what a cell holds is asserted at the top of a claim, not inside a type");
      return [intern(types, [{ refs: { first: lowerType(types, field.write), rest: [] } }])];
    }
    if (atom.a === "function") {
      const [domain, ...more] = atom.params || [];
      if (!domain || more.length) throw new TypeSyntaxError("a function takes exactly one parameter here");
      return [intern(types, [{ arrs: { arrows: [[[lowerType(types, domain)], lowerType(types, atom.result)]] } }])];
    }
    throw new TypeSyntaxError("'" + (atom.a || "type") + "' is outside the checked fragment");
  }

  function lowerType(types: any, type: any): number[] {
    if (!type || typeof type !== "object" || !Array.isArray(type.atoms)) throw new TypeSyntaxError("not a type");
    if (type.top) throw new TypeSyntaxError("'unknown' is outside the checked fragment");
    return Array.from(new Set<number>(type.atoms.flatMap((atom: any) => lowerAtom(types, atom)))).sort((a, b) => a - b);
  }

  // A point, lowered: the encoding written directly is kept as written, so a
  // label list comes back alone; a structural type comes back with the
  // current-content assertion it makes, or `null` for none, as the format
  // requires one or the other to be said.
  function lower(types: any, type: any): { type: number[]; current?: number[] | null } {
    if (Array.isArray(type)) return { type };
    const [atom, ...more] = (type && type.atoms) || [];
    const field = !more.length && atom && atom.a === "record" ? (atom.fields || [])[0] : null;
    if (field && field.name === "value" && !same(field.read, field.write)) {
      const current = lowerType(types, field.read);
      if (current.some((l) => l > 3)) throw new TypeSyntaxError("a cell holds null, true, false or undefined");
      const invariant = { ...type, atoms: [{ ...atom, fields: [{ ...field, read: field.write }] }] };
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
  function modesText(atom: any) {
    const parts = [];
    for (const key of ["call", "construct", "array"])
      if (key in atom && atom[key] !== "absent") parts.push(key + "=" + atom[key]);
    if (atom.indexes && typeof atom.indexes === "object")
      for (const kind of ["string", "number", "symbol"])
        if (kind in atom.indexes && atom.indexes[kind] !== "absent")
          parts.push(kind + "-index=" + atom.indexes[kind]);
    return parts.length ? " [" + parts.join(" ") + "]" : "";
  }
  function fullAtomText(atom: any) {
    if (!atom || typeof atom !== "object") return String(atom);
    if (atom.unsupported === true) return "(unavailable)";
    let text;
    if (atom.a === "record" && Array.isArray(atom.fields))
      text =
        "{ " +
        atom.fields
          .map((field: any) => {
            const name = field.name + (field.optional ? "?" : "");
            const read = fullTypeText(field.read);
            const write = fullTypeText(field.write);
            return read === write
              ? name + ": " + read
              : name + ": " + write + " = (" + read + ")";
          })
          .join(", ") +
        " }" +
        modesText(atom);
    else if (atom.a === "function" && Array.isArray(atom.params))
      text =
        "(" +
        atom.params.map(fullTypeText).join(", ") +
        ") => " +
        fullTypeText(atom.result) +
        modesText(atom);
    else if (PRIMITIVE.includes(atom.a) && Object.keys(atom).join() === "a")
      text = atom.a;
    else if (LITERAL[atom.a] && "v" in atom)
      text = atom.a === "stringlit" ? JSON.stringify(atom.v) : String(atom.v);
    else {
      const { and, ...rest } = atom;
      text = JSON.stringify(rest);
    }
    if (Array.isArray(atom.and) && atom.and.length)
      text += atom.and.map((other: any) => " & " + fullAtomText(other)).join("");
    return text;
  }
  function fullTypeText(type: any) {
    if (type === undefined || type === null) return "«missing»";
    if (typeof type === "string") return type;
    if (type.unsupported === true) return "(unavailable)";
    if (type.top === true) return "unknown";
    if (!Array.isArray(type.atoms)) return JSON.stringify(type);
    if (!type.atoms.length) return "never";
    return type.atoms.map(fullAtomText).join(" | ");
  }
  function printFull(type: any) {
    return fullTypeText(type);
  }

  return {
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
})();

export default surfaceTypes;
