// FIXME: missing callgraph edge for decorator calls
function myDecorator(target: any): any {
  return target;
}
class Foo {}
// @skjs-expect-error Unknown character: @ (64)
@myDecorator
