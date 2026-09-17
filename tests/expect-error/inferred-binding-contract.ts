// Baseline: SKJS currently accepts these replacements without checking the
// retained binding contract. TypeScript rejects both assignments.
function inferredPrimitiveContract(): string {
  let value = 1;
  value = "s";
  return value;
}

function inferredCallableContract(): string {
  let value = (): number => 1;
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
