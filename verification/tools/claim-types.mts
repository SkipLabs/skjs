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
  return atoms.map((atom: any) => atomText(atom, state)).join(" | ");
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
  // kind, taking the first template atom of that kind; order is not assumed.
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
    const atoms = [atom(from)];
    while (peek() === "|") {
      take("|");
      atoms.push(atom(from));
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
    if (token === "(") return arrow(from);
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
    readClaimValue,
    claimOutsideFragment,
    TypeSyntaxError,
  };
})();

export default surfaceTypes;