const seed: number = 1;
function selfInitializer(): number {
  // @ts-expect-error Variable 'seed' is used before being assigned
  const seed = seed;
  return seed;
}
function laterDeclarator(): number {
  // @ts-expect-error Variable 'seed' is used before being assigned
  const first = seed,
    seed = 2;
  return first;
}
function earlierDeclarator(): number {
  const seed = 2,
    second = seed;
  return second;
}
