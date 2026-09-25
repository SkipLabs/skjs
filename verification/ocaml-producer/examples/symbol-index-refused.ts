// A symbol index signature constrains every symbol key; the model's index
// constrains string keys only.
type Tags = { [k: symbol]: boolean };
export function same(t: Tags): Tags {
  return t;
}
