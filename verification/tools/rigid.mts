/*
 * Rigid type parameters, worked out where the report is written.
 *
 * A claim of `T` states the whole type. `T` is rigid: it has no value, nothing
 * stands for it, and the only thing known about it is its declared upper
 * bound. That bound is not in the claim — it is in the Fragment, which the
 * verifier reads beside the claims, and it is what discharges `T ≤ boolean`
 * when a function returns `value: T` at `boolean`. Drop `extends boolean` from
 * the source and the identical claim is refused, so a reader that draws the
 * claim and not the bound is showing one premise of a check and hiding the
 * other.
 *
 * Everything here happens once, at report generation. What reaches the reader
 * is already printed: it has a name and a line of surface syntax to draw, and
 * nothing to work out.
 */
import type { ClaimType } from "./source-claims.mts";
import type { Ast } from "./fragment.mts";
import surface from "./claim-text.mts";
// term-claim.mts prints a declared bound, a source type term, in the claim form.
import { claimOfTerm } from "./term-claim.mts";

/**
 * One parameter a function declares. `bound` is `null` where the source
 * declares none: an unbounded parameter is not one bounded by `unknown`, and
 * saying so would state a constraint the source never wrote.
 */
export interface RigidParameter {
  name: string;
  bound: string | null;
}

/** A function's parameters, keyed by its name span — the identity the report
 * and the claims already agree on, and the one that survives a recollection. */
export type RigidScopes = Map<string, RigidParameter[]>;

const key = (namePos: readonly number[]) => namePos.join(":");

/**
 * Which parameters a claim names.
 *
 * `ClaimType` is a closed union and each case is answered here, so a new form
 * added to the wire format stops compiling rather than silently drawing
 * nothing: a label list is ground and names none, `{param}` names exactly one,
 * and an unavailable type states no type at all.
 *
 * A name the enclosing function does not declare yields nothing. That is a
 * claim inconsistent with its source, which the verifier rejects; it is not
 * for a display tool to decide, and inventing a bound for it here would be
 * this file stating a constraint nobody wrote.
 */
export function rigidOf(
  type: ClaimType,
  scope: RigidParameter[],
): RigidParameter[] {
  const visit = (type: ClaimType, hidden: Set<string>): RigidParameter[] => {
    if (Array.isArray(type)) return [];
    if ("param" in type) {
      if (hidden.has(type.param)) return [];
      const declared = scope.find((p) => p.name === type.param);
      return declared ? [declared] : [];
    }
    if ("array" in type) return visit(type.array, hidden);
    if ("union" in type) return type.union.flatMap((t) => visit(t, hidden));
    if ("unavailable" in type) return [];
    if ("scheme" in type) {
      const seen = new Set(hidden);
      const fromBounds = type.scheme.typeParams.flatMap((p) => {
        const found = p.bound ? visit(p.bound, seen) : [];
        seen.add(p.name);
        return found;
      });
      const local = new Set([
        ...hidden,
        ...type.scheme.typeParams.map((p) => p.name),
      ]);
      return [
        ...fromBounds,
        ...visit(type.scheme.this, local),
        ...type.scheme.params.flatMap((p) => visit(p, local)),
        ...visit(type.scheme.result, local),
        ...(type.scheme.rest === null ? [] : visit(type.scheme.rest, local)),
      ].filter(
        (p, index, all) =>
          all.findIndex((q) => q.name === p.name && q.bound === p.bound) ===
          index,
      );
    }
    const unhandled: never = type;
    return unhandled;
  };
  return visit(type, new Set());
}

/**
 * Every function's parameters, read from the Fragment. The bound is printed
 * here, in the same surface syntax every other type in the report is printed
 * in, because the reader prints nothing of its own.
 */
export function rigidScopes(ast: Ast): RigidScopes {
  const scopes: RigidScopes = new Map();
  for (const fn of ast.functions)
    scopes.set(
      key(fn.namePos),
      fn.typeParams.map((p) => ({
        name: p.name,
        bound: p.bound ? surface.printType(claimOfTerm(p.bound)).text : null,
      })),
    );
  return scopes;
}

/** A function's parameters, or none where the Fragment has nothing for it. */
export const scopeOf = (
  scopes: RigidScopes,
  namePos: readonly number[],
): RigidParameter[] => scopes.get(key(namePos)) ?? [];
