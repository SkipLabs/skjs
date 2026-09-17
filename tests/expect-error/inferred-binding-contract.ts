// Every replacement preserves the inferred binding contract, even without
// capture. TypeScript also rejects these incompatible assignments.
function inferredPrimitiveContract(): string {
  let value = 1;
  // @ts-expect-error Type is not assignable to the variable's type
  value = "s";
  return value;
}

function inferredCallableContract(): string {
  let value = (): number => 1;
  // @ts-expect-error Type is not assignable to the variable's type
  value = (): string => "s";
  return value();
}

// An explicit union establishes one write contract; assignment still narrows
// the current contents, so returning the newly written string is valid.
function unionContractStillNarrows(): string {
  let value: number | string = 1;
  value = "s";
  return value;
}

// Replacing a value within the inferred contract remains valid.
function compatibleInferredReplacement(): number {
  let value = (): number => 1;
  value = (): number => 2;
  return value();
}
