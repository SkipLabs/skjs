/**
 * An arrow whose domain is empty can never be applied, so its result contract
 * is vacuous and it sits above every arrow -- `Arrow.empty` in the model,
 * proved sound, and the shape the deleted completeness result needed. SKJS
 * applies ordinary variance instead: the domains check contravariantly, then
 * `null` is not assignable to `boolean`, so it rejects. TypeScript rejects the
 * same binding for the same reason. The annotation is true in the model and
 * neither TypeScript checker accepts it.
 */
function emptyDomainEscape(): null {
  const g: (x: never) => boolean = (x: null): null => null;
  return null;
}
