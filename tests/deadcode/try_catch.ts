// Exceptional interprocedural control-flow: how a catch handler's reachability
// depends on whether the wrapped call can throw.
//
//   (A) wraps a call that ALWAYS throws  -> catch is reachable; the normal
//       continuation after the call is not.
//   (B) wraps a call that NEVER throws   -> catch is unreachable (dead).
//   (C) wraps a call that SOMETIMES throws -> both catch and continuation
//       reachable.
//
// The callee's throw behavior is propagated back through the interproc
// callback's `onThrow` state, so the analysis distinguishes all three: the
// expectations below show the catch block dead in (B) only.

function alwaysThrows(): number {
  throw new Error("boom");
}

function neverThrows(): number {
  return 1;
}

function sometimesThrows(b: boolean): number {
  if (b) {
    throw new Error("maybe");
  }
  return 2;
}

// (A) call that always throws
function wrapAlways(): number {
  try {
    const _ = alwaysThrows();
  } catch (e) {
    return -1;
  }
  return 0;
}

// (B) call that never throws
function wrapNever(): number {
  try {
    return neverThrows();
  } catch (e) {
    return -1;
  }
}

// (C) call that sometimes throws
function wrapSometimes(flag: boolean): number {
  try {
    return sometimesThrows(flag);
  } catch (e) {
    return -1;
  }
}

const a = wrapAlways();
const b = wrapNever();
const c = wrapSometimes(true);
