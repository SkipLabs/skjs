// A field without an initializer holds `undefined` from the instance's
// creation: `alias?: string` is then present at `undefined`, which an exact
// optional field of type `string` does not admit. (TypeScript accepts this.)
class Maybe {
  alias?: string;
}
export function make(): Maybe {
  return new Maybe();
}
