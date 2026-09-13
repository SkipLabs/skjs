type Id<T> = T;
function wrap(x: Id<boolean>): Id<boolean> {
  return x;
}
