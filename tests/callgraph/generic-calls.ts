// @skjs-callgraph
// fn:useIdentity: fn:identity

function identity<T>(x: T): T {
  return x;
}
function useIdentity(): number {
  return identity<number>(42);
}
