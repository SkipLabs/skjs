// @skjs-callgraph
// fn:test: static:Counter.reset
// static:Counter.reset: fn:defaultValue

function defaultValue(): number {
  return 0;
}

class Counter {
  static reset(): number {
    return defaultValue();
  }
}

function test(): number {
  return Counter.reset();
}
