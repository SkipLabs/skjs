// Two values of a function type can lack a modeled identity location.
function functionIdentity(left: () => void, right: () => void): boolean {
  return left == right;
}
