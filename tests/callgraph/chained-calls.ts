// @skjs-callgraph
// fn:chain: method:Builder.build, method:Builder.step1, method:Builder.step2

class Builder {
  step1(): Builder {
    return this;
  }
  step2(): Builder {
    return this;
  }
  build(): number {
    return 1;
  }
}
function chain(b: Builder): number {
  return b.step1().step2().build();
}
