// @skjs-callgraph
// method:MyClass.doWork: fn:helper
// static:MyClass.staticWork: fn:helper

function helper(): number {
  return 1;
}

class MyClass {
  doWork(): number {
    return helper();
  }
  static staticWork(): number {
    return helper();
  }
}
