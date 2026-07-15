// Switch pruning: a known scrutinee selects one case; the others are dead.

function classify(k: number): number {
  switch (k) {
    case 1:
      return 100;
    case 2:
      return 200;
    default:
      return 300;
  }
}

function main(): number {
  return classify(2); // case 2 -> 200; case 1 and default are dead
}
