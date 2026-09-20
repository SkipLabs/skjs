// A contextual literal must select one complete union alternative. Joining
// element types independently loses the correlation between tuple positions
// (or between all elements of one array).
function tupleUnionSecondBranch(): [number, string] | [boolean, number] {
  return [true, 0];
}

function tupleUnionCrossedElements(): [number, string] | [boolean, number] {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return [0, 0];
}

function arrayUnionCrossedElements(): number[] | string[] {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return [0, "s"];
}
