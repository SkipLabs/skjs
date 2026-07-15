// An explicit type annotation is a hard constraint: every write to the binding
// must satisfy the declared type. A binding without an annotation has an
// inferred type that instead evolves on assignment, so a same-frame write only
// narrows it and any misuse is caught where the value is read.

// FIXME: tsc rejects this write (TS2322) but SKJS currently accepts it, narrowing
// `x` to number instead of enforcing the annotation.
function annotatedWriteMustSatisfyAnnotation(): void {
  let x: string = "a";
  x = 5;
}

// A parameter's type is an annotation too, so reassigning it is checked.
// FIXME: tsc rejects this write (TS2322) but SKJS currently accepts it.
function annotatedParamWriteIsChecked(): void {
  const g = (p: string) => {
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

// Without an annotation the inferred type evolves: the write is accepted and
// `x` becomes a number. SKJS is deliberately more permissive than tsc here (tsc
// pins `let x = "a"` to `string` and rejects the write); the narrowing keeps this
// sound because reads see the written type.
function inferredWriteEvolves(): void {
  let x = "a";
  x = 5;
  const n: number = x;
}
