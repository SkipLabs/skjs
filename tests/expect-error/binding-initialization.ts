const seed: number = 1;
function selfInitializer(): number {
  // FIXME: this reads its own uninitialized binding, not the outer seed.
  const seed = seed;
  return seed;
}
function laterDeclarator(): number {
  // FIXME: the later declarator already shadows the outer seed.
  const first = seed,
    seed = 2;
  return first;
}
function earlierDeclarator(): number {
  const seed = 2,
    second = seed;
  return second;
}
