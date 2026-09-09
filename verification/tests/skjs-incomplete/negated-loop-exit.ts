/**
 * Incompleteness witness: both Boolean inputs return true, but SKJS forgets
 * the loop-exit refinement and rejects the result annotation. Local verification
 * also needs a true entry claim for flag at the final return. The incoming
 * loop-exit edge justifies that explicit refinement.
 */
function negatedVariableLoop(flag: boolean): true {
  while (!flag) {
    return true;
  }
  return flag;
}
