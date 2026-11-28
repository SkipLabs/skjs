// Captured writes to an evolving local (`let r = null` / `let r = undefined`)
// must stay sound across every control-flow shape (#840).

class EvolvingNode {
  value: number = 0;
}

function mkEvolvingNode(): EvolvingNode {
  return new EvolvingNode();
}

// Issue #840 comment: captured write introduces the first non-null value while
// the binding is still null; after calling the closure, the enclosing scope
// cannot still read the binding as `null`.
function capturedWriteFirstNonNull(): void {
  let x = null;
  const write = (): void => {
    x = "s";
  };
  write();
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type 'string'
  // @skjs-expect-error-line3 is not assignable to type 'null'
  // @skjs-expect-error-line4 This call may have changed the value of 'x'
  const n: null = x;
  void n;
}

// Capture defined before evolution: `g` is created while `r` is still `null`,
// then `r = mkEvolvingNode()` runs, then `g()` mutates `r` to `5`.
function captureBeforeEvolution(): void {
  let r = null;
  const g = () => {
    r = 5;
  };
  r = mkEvolvingNode();
  const before: number = r.value;
  void before;
  g();
  // @skjs-expect-error Property 'value' does not exist on this type
  // @skjs-expect-error-line3 This call may have changed the value of 'r'
  const after: number = r.value;
  void after;
}

// Two closures writing different types to an evolving local: after both run,
// `r` cannot be assumed to be `EvolvingNode` even after a null check.
function twoClosuresWriteEvolving(): void {
  let r = null;
  const g1 = () => {
    r = mkEvolvingNode();
  };
  const g2 = () => {
    r = 5;
  };
  g1();
  g2();
  if (r !== null) {
    // @skjs-expect-error Property 'value' does not exist on this type
    // @skjs-expect-error-line3 This call may have changed the value of 'r'
    const v: number = r.value;
    void v;
  }
}

// Same-type evolution across closures and outer scope remains valid when
// guarded against null.
function evolvingCompatibleClosureWrites(): number {
  let r = null;
  const setNode = () => {
    r = mkEvolvingNode();
  };
  setNode();
  if (r !== null) {
    return r.value;
  }
  return 0;
}

// Evolving local mutated by a closure called inside a `while` loop: iteration 1
// sees `EvolvingNode`, `g()` sets `r = 5`, iteration 2 reads `r.value` on `5`.
function whileLoopCallsMutatingClosure(cond: boolean): void {
  let r = null;
  r = mkEvolvingNode();
  const g = () => {
    r = 5;
  };
  while (cond) {
    // @skjs-expect-error Property 'value' does not exist on this type
    // @skjs-expect-error-line3 This call may have changed the value of 'r'
    const v: number = r.value;
    void v;
    g();
  }
}

// Same in a `for` loop body.
function forLoopCallsMutatingClosure(): void {
  let r = null;
  r = mkEvolvingNode();
  const g = () => {
    r = 5;
  };
  for (let i = 0; i < 2; i++) {
    // @skjs-expect-error Property 'value' does not exist on this type
    // @skjs-expect-error-line3 This call may have changed the value of 'r'
    const v: number = r.value;
    void v;
    g();
  }
}

// Same when the mutating closure is called in the `for` increment.
function forIncrCallsMutatingClosure(): void {
  let r = null;
  r = mkEvolvingNode();
  const g = () => {
    r = 5;
  };
  for (let i = 0; i < 2; g()) {
    // @skjs-expect-error Property 'value' does not exist on this type
    // @skjs-expect-error-line3 This call may have changed the value of 'r'
    const v: number = r.value;
    void v;
    i++;
  }
}

// Same in a `for...in` loop.
function forInCallsMutatingClosure(obj: { [k: string]: number }): void {
  let r = null;
  r = mkEvolvingNode();
  const g = () => {
    r = 5;
  };
  for (const k in obj) {
    void k;
    // @skjs-expect-error Property 'value' does not exist on this type
    // @skjs-expect-error-line3 This call may have changed the value of 'r'
    const v: number = r.value;
    void v;
    g();
  }
}

// Same when the loop header itself reads `r` before the body calls `g()`.
function whileHeaderReadsMutatedEvolving(): void {
  let r = null;
  r = mkEvolvingNode();
  const g = () => {
    r = 5;
  };
  // @skjs-expect-error Property 'value' does not exist on this type
  // @skjs-expect-error-line3 This call may have changed the value of 'r'
  while (r.value > 0) {
    g();
  }
}

// Same when the loop also directly writes `r = mkEvolvingNode()` alongside `g()`.
function whileLoopDirectAndClosureWrite(cond: boolean): void {
  let r = null;
  r = mkEvolvingNode();
  const g = () => {
    r = 5;
  };
  while (cond) {
    // @skjs-expect-error Property 'value' does not exist on this type
    // @skjs-expect-error-line3 This call may have changed the value of 'r'
    const v: number = r.value;
    void v;
    r = mkEvolvingNode();
    g();
  }
}

// Annotated captured local mutated by a closure called inside a loop.
function whileLoopAnnotatedCapturedClosure(cond: boolean): void {
  let r: EvolvingNode | null = null;
  r = mkEvolvingNode();
  const g = () => {
    r = null;
  };
  while (cond) {
    // @skjs-expect-error Property access is not allowed on this type
    // @skjs-expect-error-line2 This has type 'null'
    // @skjs-expect-error-line3 This call may have changed the value of 'r'
    const v: number = r.value;
    void v;
    g();
  }
}

// Unannotated concrete-primitive captured local narrowed before a loop whose
// body mutates it through a closure.
function whileLoopConcretePrimitiveClosure(cond: boolean): void {
  let x = 1;
  const g = () => {
    x = 2;
  };
  if (x === 1) {
    while (cond) {
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      // @skjs-expect-error-line2 Full type 'number'
      // @skjs-expect-error-line3 is not assignable to specific type '1'
      // @skjs-expect-error-line4 This call may have changed the value of 'x'
      const one: 1 = x;
      void one;
      g();
    }
  }
}

// Object field refinement must not survive a loop that mutates the field or
// invokes a call that may mutate it.
function whileLoopMutatesRefinedField(cond: boolean): void {
  const cell: { v: number | null } = { v: 1 };
  if (cell.v !== null) {
    while (cond) {
      // @ts-expect-error Type of value is not assignable to the variable's type annotation
      // @skjs-expect-error-line2 Type 'null'
      // @skjs-expect-error-line3 is not assignable to type 'number'
      // @skjs-expect-error-line4 This write may have changed a property of 'cell'
      const n: number = cell.v;
      void n;
      cell.v = null;
    }
  }
}

function whileLoopCallsFieldMutator(cond: boolean, clear: () => void): void {
  const cell: { v: number | null } = { v: 1 };
  if (cell.v !== null) {
    while (cond) {
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      // @skjs-expect-error-line2 Type 'null'
      // @skjs-expect-error-line3 is not assignable to type 'number'
      // @skjs-expect-error-line4 This call may have changed a property of 'cell'
      const n: number = cell.v;
      void n;
      clear();
    }
  }
}

// Positive: an uncaptured evolving local is NOT mutated by an opaque call inside
// a loop, so its pre-loop narrowing stays valid.
function whileLoopUncapturedEvolvingCall(
  cond: boolean,
  noop: () => void,
): void {
  let r = null;
  r = mkEvolvingNode();
  while (cond) {
    const v: number = r.value;
    void v;
    noop();
  }
}

// Positive: an uncaptured annotated local is NOT mutated by an opaque call.
function whileLoopUncapturedAnnotatedCall(
  cond: boolean,
  noop: () => void,
): void {
  let r: EvolvingNode | null = null;
  r = mkEvolvingNode();
  while (cond) {
    const v: number = r.value;
    void v;
    noop();
  }
}

// Positive: a captured evolving local in a loop with no writes and no call
// effects keeps its pre-loop narrowing.
function whileLoopCapturedNoEffects(cond: boolean): void {
  let r = null;
  r = mkEvolvingNode();
  const g = () => {
    r = 5;
  };
  void g;
  let count = 0;
  while (cond) {
    const v: number = r.value;
    count += v;
  }
  void count;
}
