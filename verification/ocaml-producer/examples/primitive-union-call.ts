// Each shape's `toString` takes its own receiver: a call through the union
// of the two members is not yet dispatched by shape.
function unionToString(x: string | number): string {
  return x.toString();
}
