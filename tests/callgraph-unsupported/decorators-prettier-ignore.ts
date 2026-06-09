// FIXME: missing callgraph edge for decorator calls
// skjs-callgraph
// toplevel: fn:myDecorator
function myDecorator(target: any): any {
  return target;
}
class Foo {}
// @skjs-expect-error Invalid character '@' (char code 64)
@myDecorator
