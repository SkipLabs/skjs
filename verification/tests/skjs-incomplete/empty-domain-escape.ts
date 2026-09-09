/**
 * A function whose domain is empty can never be applied, so its result
 * contract is vacuous and it sits above every arrow. The model has this as
 * `Arrow.empty`, proved sound, and the deleted completeness result needed it
 * with exactly this shape.
 *
 * SKJS applies ordinary variance instead: it checks the domains
 * contravariantly, accepts `never <= null`, then compares the results and
 * reports that `null` is not assignable to `boolean`. TypeScript rejects the
 * same binding for the same reason, so this is an annotation that is true in
 * the model and that neither TypeScript checker accepts. See F1 in
 * ../../SUBTYPING.md.
 */
function emptyDomainEscape(): null {
  const g: (x: never) => boolean = (x: null): null => null;
  return null;
}
