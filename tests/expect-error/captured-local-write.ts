// Assignments to a captured enclosing-function local from inside a lambda body
// must be checked against the binding's declared (widened) type at the write
// site — the lambda may run at any time, so the narrowing it performs cannot be
// trusted and the write itself has to stay within the declared type. This is
// distinct from the stale-narrowing family (#597/#598/#599): here the write is
// type-incorrect, not merely a refinement that goes stale (#769).

// A captured local declared `string`, written a `number` inside the lambda.
// FIXME: tsc rejects this write (TS2322) but SKJS currently accepts it (#769).
function capturedWriteWrongType(): void {
  let x: string = "a";
  const g = () => {
    x = 5;
  };
  g();
}

// The same violation across two nested lambda boundaries.
// FIXME: tsc rejects this write (TS2322) but SKJS currently accepts it (#769).
function capturedWriteWrongTypeNested(): void {
  let x: string = "a";
  const g = () => {
    const h = () => {
      x = 5;
    };
    h();
  };
}

// A sound captured write of the widened declared type is accepted. `let x = "a"`
// widens to `string`, so writing another `string` inside the lambda is fine.
function capturedWriteCorrectType(): void {
  let x = "a";
  const g = () => {
    x = "b";
  };
  g();
}

// A captured write of a value within the declared union is accepted.
function capturedWriteWithinDeclaredUnion(): void {
  let x: string | number = "a";
  const g = () => {
    x = 5;
  };
  g();
}

// The write is checked against the declared type, not the type narrowed at the
// point the lambda is defined: `null` is a valid `string | null` even though `x`
// is narrowed to `string` where the lambda is created.
function capturedWriteValidAgainstDeclaredType(): void {
  let x: string | null = "a";
  if (x !== null) {
    const g = () => {
      x = null;
    };
    g();
  }
}

// A parameter is local to the lambda's own frame, so reassigning it still
// narrows (it is not a captured write and is not checked against the annotation).
function paramReassignNarrowsInLambda(): void {
  const g = (p: string | number) => {
    p = 5;
    const z: number = p;
  };
}

// The check applies to every captured write, not only the first: an earlier
// write that localizes the variable inside the lambda must not hide a later
// wrong-typed one.
// FIXME: tsc rejects the second write (TS2322) but SKJS currently accepts it (#769).
function capturedWriteWrongTypeAfterLocalWrite(): void {
  let x: string = "a";
  const g = () => {
    x = "b";
    x = 5;
  };
  g();
}

// A default-parameter initializer of an arrow captures enclosing locals just
// like the body does, so a wrong-typed write there is checked the same way.
// FIXME: tsc rejects this write (TS2322) but SKJS currently accepts it (#769).
function capturedWriteInDefaultParam(): void {
  let x: string = "a";
  const g = (y: number = (x = 5)): void => {
    void y;
  };
  g();
}
