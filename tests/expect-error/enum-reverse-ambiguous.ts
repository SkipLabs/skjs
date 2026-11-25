// Access-time counterpart of the declaration-time no-duplicate-enum-values
// warning (#787): reading a reverse mapping whose literal key names more than
// one member is ambiguous — at runtime `Same[0]` resolves to the
// last-declared member, so the earlier one is unreachable via the reverse
// mapping.

enum Same {
  A = 0,
  // @skjs-expect-warning Duplicate enum member value 0
  B = 0,
}

function readAmbiguous(): string {
  return Same[0];
}

enum Distinct {
  A = 0,
  B = 1,
}

function readDistinct(): string {
  return Distinct[0];
}
