// FIXME: missing callgraph edge for tagged template calls
function tag(strings: TemplateStringsArray): string {
  return strings[0];
}
// @skjs-expect-error Expected token a variable name
const x: string = tag`hello`;
