// @skjs-callgraph
// fn:exported: fn:helper

function helper(): number {
  return 1;
}
export function exported(): number {
  return helper();
}
