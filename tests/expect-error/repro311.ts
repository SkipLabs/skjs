class MyClass {
  constructor(public x: number = 0) {}
}

function perform(
  ctor: new (...params: number[]) => MyClass,
  ...params: number[]
): void {
  console.log(new ctor(...params).x);
}

perform(MyClass, 3);
