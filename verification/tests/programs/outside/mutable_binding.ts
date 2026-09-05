// Outside the fragment: the gate must reject `let`.
function pick(x: string): string {
  let y = x;
  return y;
}
