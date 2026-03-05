// @skjs-callgraph
// ctor:Widget: fn:init
// fn:makeWidget: static:Widget.constructor

function init(): void {}

class Widget {
  constructor() {
    init();
  }
}

function makeWidget(): Widget {
  return new Widget();
}
