/**
 * Incompleteness witness: both Boolean inputs return true, but SKJS forgets
 * the loop-exit refinement and rejects the result annotation. The verifier now
 * accepts the original broad claims: its checked branch-value fact justifies
 * the true return. Explicitly strengthened claims remain a valid repair too.
 */
function negatedVariableLoop(flag: boolean): true {
  while (!flag) {
    return true;
  }
  return flag;
}
