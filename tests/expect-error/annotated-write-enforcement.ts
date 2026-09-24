// An explicit type annotation is a hard constraint: every write to the binding
// must satisfy the declared type. A binding without an annotation has an
// inferred type that instead evolves on assignment, so a same-frame write only
// narrows it and any misuse is caught where the value is read.

function annotatedWriteMustSatisfyAnnotation(): void {
  let x: string = "a";
  // @ts-expect-error Type is not assignable to the variable's type
  x = 5;
}

// A parameter's type is an annotation too, so reassigning it is checked.
function annotatedParamWriteIsChecked(): void {
  const g = (p: string) => {
    // @ts-expect-error Type is not assignable to the variable's type
    p = 5;
  };
}

// A write within the declared type is accepted, and still narrows for later
// reads in the same frame.
function annotatedWriteWithinDeclaredTypeNarrows(): void {
  let x: string | number = "a";
  x = 5;
  const n: number = x;
}

// An inferred concrete type is a write contract too, even without capture.
// TypeScript also rejects replacing the string with a number.
function inferredWriteEvolves(): void {
  let x = "a";
  // @ts-expect-error Type is not assignable to the variable's type
  x = 5;
  const n: number = x;
}
