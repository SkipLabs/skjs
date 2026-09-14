function clearEffect(x: { value: number | null }): boolean {
  x.value = null;
  return true;
}
function directEffect(x: { value: number | null }): number {
  if (x.value === null) return 0;
  void clearEffect(x);
  return x.value;
}
function methodEffect(
  x: { value: number | null },
  action: { run: () => void },
): number {
  if (x.value === null) return 0;
  action.run();
  return x.value;
}
class EffectConstructor {
  constructor(run: () => void) {
    run();
  }
}
function constructorEffect(x: { value: number | null }): number {
  if (x.value === null) return 0;
  const action = new EffectConstructor(() => {
    x.value = null;
  });
  return x.value;
}
async function suspensionEffect(
  x: { value: number | null },
  ready: Promise<void>,
): Promise<number> {
  if (x.value === null) return 0;
  await ready;
  return x.value;
}
function conditionEffect(x: { value: number | null }): number {
  if (x.value !== null && clearEffect(x)) return x.value;
  return 0;
}
function snapshotAcrossEffect(x: { value: number | null }): number {
  if (x.value === null) return 0;
  const snapshot = x.value;
  void clearEffect(x);
  return snapshot;
}
function freshCheckAfterEffect(x: { value: number | null }): number {
  void clearEffect(x);
  if (x.value === null) return 0;
  return x.value;
}

function privateScalar(x: number | null, action: () => void): number {
  if (x === null) return 0;
  action();
  return x;
}
function postCallGuard(
  x: { value: number | null },
  action: () => boolean,
): number {
  if (action() && x.value !== null) return x.value;
  return 0;
}
