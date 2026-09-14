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

function laterStatement(): number {
  // FIXME: the later local already shadows the outer seed.
  const first = seed;
  const seed = 2;
  return first;
}

// The condition runs before entering the block containing the local seed.
function conditionBeforeLocal(): number {
  if (seed === 1) {
    const seed = 2;
    return seed;
  }
  return 0;
}
