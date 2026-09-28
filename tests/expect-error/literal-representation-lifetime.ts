// A default decision reads the existing element type; it must not try to
// infer a different element type merely to decide whether undefined fits.
function queryFreshLiteralDefault(seed: number): number {
  // @skjs-expect-warning This default is unreachable because the element cannot be 'undefined'
  const [value = 0] = [seed];
  return value;
}
// Structural validation must commit the literal representation before a
// length contract can escape through another view.
function queryLiteralLengthView(seed: number): 1 {
  const items = [seed];
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const view: { readonly length: 1 } = items;
  items.push(seed);
  return view.length;
}

// Both literal identities remain reachable through the conditional alias.
function queryConditionalLiteralLengthView(seed: number, pick: boolean): 1 {
  const first = [seed];
  const second = [seed + 1];
  const items = pick ? first : second;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const view: { readonly length: 1 } = items;
  first.push(seed);
  second.push(seed);
  return view.length;
}

function queryLiteralBroadLengthView(seed: number): number {
  const items = [seed];
  const view: { readonly length: number } = items;
  items.push(seed);
  return view.length;
}

// Mixed await must establish the literal form before retaining its shape.
async function queryMixedAwaitedLiteralLength(
  seed: number,
  pick: boolean,
  pending: Promise<number>,
): Promise<1> {
  const items = [seed];
  // @skjs-expect-warning 'await' can only be applied to a Promise
  const view = await (pick ? items : pending);
  if (typeof view === "number") return 1;
  items.push(seed);
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return view.length;
}

async function queryMixedAwaitedLiteralBroadLength(
  seed: number,
  pick: boolean,
  pending: Promise<number>,
): Promise<number> {
  const items = [seed];
  // @skjs-expect-warning 'await' can only be applied to a Promise
  const view = await (pick ? items : pending);
  if (typeof view === "number") return view;
  items.push(seed);
  return view.length;
}
