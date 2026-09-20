// A contextual literal must select one complete union alternative. Joining
// element types independently loses the correlation between tuple positions
// (or between all elements of one array).
function tupleUnionSecondBranch(): [number, string] | [boolean, number] {
  return [true, 0];
}

function tupleUnionCrossedElements(): [number, string] | [boolean, number] {
  // FIXME: SKJS currently accepts the product of the alternatives' elements.
  return [0, 0];
}

function arrayUnionCrossedElements(): number[] | string[] {
  // FIXME: SKJS currently accepts Array<number | string> as this union.
  return [0, "s"];
}
