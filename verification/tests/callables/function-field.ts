/**
 * One function value carries an initialized mutable field. An alias observes
 * the write without losing callability. Explicit Object.assign type arguments
 * avoid SKJS's current inference of never for the unannotated intersection.
 */
function callableField(seed: boolean): boolean {
  const f = Object.assign<(next: boolean) => boolean, { value: boolean }>(
    (next: boolean): boolean => next,
    { value: seed },
  );
  const alias = f;
  f.value = !seed;
  return alias(alias.value);
}
