// SKJS does not retain the false edge of this negated loop condition.
function negatedVariableLoop(flag: boolean): true {
  while (!flag) {
    return true;
  }
  return flag;
}
