function label(x: string | null): string {
  const fallback: string = "missing";
  if (x === null) {
    return fallback;
  }
  const found = x;
  return found;
}

function shout(x: string | null): string {
  const s = label(x);
  return s;
}
