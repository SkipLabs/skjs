/** A source type term in the structural claim form, for tools that display a
 * source annotation or offer it as a template for a claim. The verifier reads
 * annotations itself (EquationLowering.lean); this rendering decides nothing. */
import type { Atom, ClaimType } from "./claim.mts";
import type { TypeTerm } from "./declaration-types.mts";

const never: ClaimType = { top: false, atoms: [] };

export function claimOfTerm(term: TypeTerm): ClaimType {
  const one = (atom: Atom): ClaimType => ({ top: false, atoms: [atom] });
  switch (term.k) {
    case "atom":
      if (term.name === "unknown") return { top: true, atoms: [] };
      if (term.name === "never") return never;
      // Every object is several graph clauses (EquationLowering.lean), as
      // `callable` is.
      if (term.name === "object") throw Error("the object type has no claim form");
      return one({ a: term.name });
    case "literal":
      return one(term.name === "true" || term.name === "false"
        ? { a: "booleanlit", v: term.name }
        : term.name === "bigint" ? { a: "bigintlit", v: term.text }
        : { a: term.name === "number" ? "numberlit" : "stringlit", v: term.text });
    case "unique":
      throw Error("a unique symbol type has no claim form: it is a graph row");
    case "union": {
      const parts = term.parts.map(claimOfTerm);
      if (parts.some(p => p.top)) return { top: true, atoms: [] };
      return { top: false, atoms: parts.flatMap(p => p.atoms) };
    }
    case "intersection": {
      const [head, ...rest] = term.parts.map(p => claimOfTerm(p).atoms[0]);
      if (!head || (head.a !== "record" && head.a !== "function"))
        throw Error("intersection outside the claim form");
      return one({ ...head, and: rest.filter(a => a !== undefined) });
    }
    case "array":
      return one({ a: "array", presence: term.presence, required: [], optional: [], rest: claimOfTerm(term.element),
        readonly: term.readonly });
    case "tuple":
      return one({ a: "array", presence: term.presence, required: term.required.map(claimOfTerm),
        optional: term.optional.map(claimOfTerm),
        rest: term.rest ? claimOfTerm(term.rest) : null, readonly: term.readonly });
    case "function":
      if (term.effect !== "unrestricted") throw Error("a qualified callable annotation requires graph lowering");
      return one({ a: "function",
        this: term.receiver ? claimOfTerm(term.receiver) : { top: true, atoms: [] },
        params: term.params.map(claimOfTerm),
        ...(term.rest ? { rest: claimOfTerm(term.rest) } : {}),
        result: claimOfTerm(term.result), construct: "unknown", array: "unknown" });
    case "constructor":
      if (term.rest) throw new Error("a construct signature with a rest has no claim form");
      return one({ a: "constructor", params: term.params.map(claimOfTerm),
        result: claimOfTerm(term.result) });
    case "pack":
      throw new Error("a pack parameter has no claim form");
    case "object":
      if (term.numberIndex || term.symbolIndex)
        throw new Error("a number or symbol index signature has no claim form: it is graph rows");
      return one({ a: "record",
        fields: term.fields.map(f => {
          const read = claimOfTerm(f.type);
          return { name: f.name, optional: f.optional, read, write: f.readonly ? never : read };
        }),
        indexes: { string: "absent", number: "absent", symbol: "absent" },
        ...(term.stringIndex ? { indexSignature: { read: claimOfTerm(term.stringIndex.value),
          write: never } } : {}),
        call: "unknown", construct: "unknown", array: "unknown" });
    case "binder":
      return one({ a: "param", name: term.name });
    case "reference":
      return one({ a: "alias", name: term.reference.name, args: term.args.map(claimOfTerm) });
    case "self":
    case "parameter":
    case "scheme":
    case "callable":
      throw Error(`declaration syntax '${term.k}' outside a declaration`);
  }
}
