/**
 * Incompleteness witness: both Boolean inputs return true, but SKJS forgets
 * the loop-exit refinement and rejects the result annotation. Repair the final
 * flag binding and returned-expression claims to true; the verifier then
 * accepts them independently.
 */
function negatedVariableLoop(flag: boolean): true {
  while (!flag) {
    return true;
  }
  return flag;
}
