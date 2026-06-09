function testAssign(): void {
  const wide = (x: string | number): void => {
    console.log(x);
  };
  const narrow = (x: string): void => {
    console.log(x);
  };

  const ok: (x: string) => void = wide;
  ok("hello");

  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: (x: string | number) => void = narrow;
  bad(1);
}

function takesString(cb: (x: string) => void): void {
  cb("a");
}

function takesStringOrNumber(cb: (x: string | number) => void): void {
  cb("a");
}

function testArgs(): void {
  const wide = (x: string | number): void => {
    console.log(x);
  };
  const narrow = (x: string): void => {
    console.log(x);
  };

  takesString(wide);
  // @skjs-expect-error Invalid call
  takesStringOrNumber(narrow);
}

function testObjectUnion(): void {
  const wide = (x: { a: string } | { b: number }): void => {
    if ("a" in x) {
      // @skjs-expect-error Property 'a' was confirmed present by `in` but its declaration is unknown — accessing it is unsafe (it could be private)
      console.log(x.a);
    } else {
      console.log(x.b);
    }
  };
  const narrow = (x: { a: string }): void => {
    console.log(x.a);
  };

  const ok: (x: { a: string }) => void = wide;
  ok({ a: "ok" });

  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: (x: { a: string } | { b: number }) => void = narrow;
  bad({ b: 1 });
}
