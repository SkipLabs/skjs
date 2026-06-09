// FIXME: missing callgraph edge for tagged template calls
// skjs-callgraph
// toplevel: fn:tag
function tag(strings: TemplateStringsArray): string {
  return strings[0];
}
// @skjs-expect-error 'a variable name' expected
const x: string = tag`hello`;
