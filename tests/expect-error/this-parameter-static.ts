// Static methods have no `this` (NoThis): like a free function they are freely
// callable, detachable, and usable where a no-`this` function type is expected.

class StaticHolder {
  static make(): number {
    return 1;
  }
}

function callsCb(cb: () => number): number {
  return cb();
}

// Detached and free-called.
export function staticDetach(): number {
  const f = StaticHolder.make;
  return f();
}

// Passed as a no-`this` callback.
export function staticAsCallback(): number {
  return callsCb(StaticHolder.make);
}

// Assigned into a no-`this` function type.
export function staticAssignToNoThis(): number {
  const f: () => number = StaticHolder.make;
  return f();
}
