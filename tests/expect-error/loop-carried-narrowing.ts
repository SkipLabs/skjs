// The next iteration can read null despite the pre-loop string narrowing.
function staleLoopRead(x: string | null, again: boolean): void {
  if (x !== null) {
    while (again) {
      // @ts-expect-error Type of value is not assignable to the variable's type annotation
      const text: string = x;
      x = null;
    }
  }
}

// The increment is part of the back edge, even when the body continues.
function staleIncrementRead(x: string | null, again: boolean): void {
  if (x !== null) {
    for (; again; x = null) {
      // TypeScript also accepts this stale read.
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const text: string = x;
      continue;
    }
  }
}

function staleForOfRead(x: string | null, values: number[]): void {
  if (x !== null) {
    for (const value of values) {
      // A fresh iteration variable does not stabilize an outer binding.
      // @ts-expect-error Type of value is not assignable to the variable's type annotation
      const text: string = x;
      x = null;
    }
  }
}

// A condition checked on each iteration establishes a fresh narrowing.
function guardedLoopRead(x: string | null, again: boolean): void {
  while (x !== null && again) {
    const text: string = x;
    x = null;
  }
}

// Preserve facts about bindings that the loop never assigns.
function unchangedLoopRead(x: string | null, again: boolean): void {
  if (x !== null) {
    let count: number = 0;
    while (again) {
      const text: string = x;
      count += 1;
    }
  }
}

// The for condition is rechecked after its increment, just like a while guard.
function guardedIncrementRead(x: string | null): void {
  if (x !== null) {
    for (; x !== null; x = null) {
      const text: string = x;
    }
  }
}

// #869: member refinements on const/this bindings must not survive a loop
// whose body or header writes a property through an alias or invokes a call.
function staleConstMemberInForLoop(): void {
  const e: { x: number } = { x: 1 };
  const f: { x: number } = e;
  if (e.x === 1) {
    for (let i = 0; i < 2; i++) {
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const z: 1 = e.x;
      f.x = 99;
    }
  }
}

function staleConstMemberInForUpdate(): void {
  const e: { x: number } = { x: 1 };
  const f: { x: number } = e;
  if (e.x === 1) {
    for (let i = 0; i < 2; f.x = 99) {
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const z: 1 = e.x;
      i++;
    }
  }
}

function staleConstMemberInWhileLoop(): void {
  const e: { x: number } = { x: 1 };
  const f: { x: number } = e;
  if (e.x === 1) {
    let i = 0;
    while (i < 2) {
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const z: 1 = e.x;
      f.x = 99;
      i++;
    }
  }
}

function staleConstMemberInForInLoop(o: { a: number; b: number }): void {
  const e: { x: number } = { x: 1 };
  const f: { x: number } = e;
  if (e.x === 1) {
    for (const k in o) {
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const z: 1 = e.x;
      f.x = 99;
    }
  }
}

class LoopMemberBox {
  x: number = 1;
  mutateInLoop(f: LoopMemberBox): void {
    if (this.x === 1) {
      for (let i = 0; i < 2; i++) {
        // @skjs-expect-error Type of value is not assignable to the variable's type annotation
        const z: 1 = this.x;
        f.x = 99;
      }
    }
  }
}

function staleConstMemberInLoopWithCall(mutate: () => void): void {
  const e: { x: number } = { x: 1 };
  if (e.x === 1) {
    for (let i = 0; i < 2; i++) {
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const z: 1 = e.x;
      mutate();
    }
  }
}

function staleLetMemberInLoopWithCall(mutate: () => void): void {
  let e: { x: number } = { x: 1 };
  if (e.x === 1) {
    for (let i = 0; i < 2; i++) {
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const z: 1 = e.x;
      mutate();
    }
  }
}

function staleMemberInForCond(): void {
  const e: { x: number } = { x: 1 };
  const f: { x: number } = e;
  if (e.x === 1) {
    const need1 = (n: 1): boolean => n === 1;
    // @skjs-expect-error Argument is not assignable to the parameter's type
    for (let i = 0; i < 2 && need1(e.x); i++) {
      f.x = 99;
    }
  }
}

function staleMemberInWhileCond(): void {
  const e: { x: number } = { x: 1 };
  const f: { x: number } = e;
  if (e.x === 1) {
    let i = 0;
    const need1 = (n: 1): boolean => n === 1;
    // @skjs-expect-error Argument is not assignable to the parameter's type
    while (i < 2 && need1(e.x)) {
      f.x = 99;
      i++;
    }
  }
}

// A non-null refinement on a const binding cannot be undone by property writes
// or calls, so it stays valid across the loop.
function preservedConstNonNullInLoop(
  f: { x: number },
  mutate: () => void,
): void {
  const e: { x: number } | null = { x: 1 };
  if (e !== null) {
    for (let i = 0; i < 2; i++) {
      const g: { x: number } = e;
      f.x = 99;
      mutate();
    }
  }
}

// A loop with neither property writes nor calls preserves pre-loop member
// refinements.
function preservedMemberInPureLoop(): void {
  const e: { x: number } = { x: 1 };
  if (e.x === 1) {
    let sum = 0;
    for (let i = 0; i < 2; i++) {
      const z: 1 = e.x;
      sum += z;
    }
  }
}

// Re-checking the member in the loop condition re-establishes the refinement.
function guardedMemberInWhileLoop(e: { x: number }, f: { x: number }): void {
  while (e.x === 1) {
    const z: 1 = e.x;
    f.x = 99;
  }
}
