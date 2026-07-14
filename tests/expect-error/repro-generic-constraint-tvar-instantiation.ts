// Minimal repro: instantiating a constrained type alias with a type-variable argument
// (introduced by inference) should not permanently close that variable to its constraint.
//
// This is a reduced version of the "Mapper<K extends Json>" / "Collection.map" pattern.

type StrOrNum = string | number;

type Mapper<K extends StrOrNum> = { map(key: string): K };

interface Collection {
  map<K extends StrOrNum>(mapper: Mapper<K>): K;
}

export function reproGenericConstraintTVarInstantiation(
  col: Collection,
): string {
  const m: Mapper<string> = { map: (_k: string): string => "x" };
  // If K were incorrectly closed to StrOrNum during constraint checking,
  // the return type here would be StrOrNum (too wide) instead of string.
  const s: string = col.map(m);
  return s;
}
