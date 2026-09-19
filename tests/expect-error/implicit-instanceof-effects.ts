// Symbol.hasInstance is an implicit method call, with ordinary call effects.
class EffectfulInstance {
  static [Symbol.hasInstance](x: { value: number | null }): boolean {
    x.value = null;
    return true;
  }
}

// FIXME: these three reads retain field facts from before the implicit call.
function implicitInstanceEffect(x: { value: number | null }): number {
  if (x.value === null) return 0;
  const matched = x instanceof EffectfulInstance;
  return x.value;
}
function instanceConditionReplay(x: { value: number | null }): number {
  if (x.value !== null && x instanceof EffectfulInstance) return x.value;
  return 0;
}
function instanceComputedRead(x: { value: number | null }): number {
  if (x.value === null) return 0;
  return x[x instanceof EffectfulInstance ? "value" : "value"];
}

function instanceScalarSnapshot(x: { value: number | null }): number {
  if (x.value === null) return 0;
  const value = x.value;
  const matched = x instanceof EffectfulInstance;
  return value;
}
function instanceFreshCheck(x: { value: number | null }): number {
  const matched = x instanceof EffectfulInstance;
  if (x.value === null) return 0;
  return x.value;
}

class NumericInstance {
  static [Symbol.hasInstance](x: { value: number }): boolean {
    return x.value.toFixed(0) === "0";
  }
}
// FIXME: the implicit call currently bypasses the hook's argument contract.
function instanceHookArgument(x: { other: number }): boolean {
  return x instanceof NumericInstance;
}
function instanceHookCompatibleArgument(x: { value: number }): boolean {
  return x instanceof NumericInstance;
}
