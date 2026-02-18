// Stale seenSub cache in Subst save/restore causes unsound type inference.
//
// Subst::save()/restore() (TTypeSubst.sk) only saves `version` and `values`,
// but NOT `seenSub`, `seenInter`, or `seenUnion`. After restore(), these caches
// contain entries computed with TVar bindings that no longer exist.
//
// TType::isSub (TTypeSubtyping.sk:878-885) checks subst.seenSub before doing
// any work. If a (u1, u2) pair was previously checked and succeeded, it returns
// STOk() immediately — regardless of whether TVar bindings have changed since.
//
// The constraint check in TEnv::instantiate (TEnv.sk:133-146) uses save/restore:
//   savedSubst = subst.save();
//   TType::isSub(subst, this, targ, cstrTy) → succeeds, grows TVars, cached
//   subst.restore(savedSubst) → TVar growth undone, but seenSub entry persists
//
// Combined with constraint-based narrowing (U intersected with its bound), this
// produces actual unsoundness: SKJS assigns type `number` to a value that is
// `"hello"` (a string) at runtime.
//
// Detailed trace for testUnsound:
//
//   getFirst({ value: "hello" }, { value: 42 })
//   where getFirst<U>(x: Constrained<U>, y: Constrained<U>): Constrained<U>
//
//   Iteration 1:
//     arg[0] vs Constrained<TVar_U>:
//       expand Constrained<TVar_U> → tenv.instantiate:
//         save(). TVar_U is unbound.
//         isSub(TVar_U_type, number_type) → grows U to number → STOk()
//         seenSub gets (TVar_U_type, number_type)
//         restore() → U unbound again, seenSub entry persists
//       structural: "hello" <: TVar_U → grows U to "hello"
//       seenSub gets (arg0_type, Constrained_TVar_U_type)   [top-level cache]
//
//     arg[1] vs Constrained<TVar_U>:
//       expand Constrained<TVar_U> → tenv.instantiate:
//         save(). TVar_U = "hello".
//         isSub(TVar_U_type, number_type) → seenSub HIT → STOk()
//         [BUG: "hello" <: number would FAIL, but check is skipped]
//         restore()
//       structural: 42 <: TVar_U → grows U to "hello" | 42
//
//   Iteration 2 (fixpoint):
//     arg[0]: seenSub HIT → STOk() [entire check skipped]
//     arg[1]: seenSub HIT → STOk() [entire check skipped]
//     U stable → exit loop
//
//   Constraint narrowing: U = ("hello" | 42) & number = 42
//   Return type: Constrained<42> — but getFirst returns x, whose value is "hello"!
//
//   Result: box.value has type 42 but runtime value "hello". Unsound.

// ============================================================
// Setup
// ============================================================

interface Constrained<T extends number> {
  value: T;
}

function getFirst<U>(x: Constrained<U>, y: Constrained<U>): Constrained<U> {
  return x;
}

// ============================================================
// FIXME: Unsound — n has type number but runtime value "hello"
//
// getFirst returns x (first arg), so box = { value: "hello" }.
// But SKJS infers U = 42 (constraint narrows "hello" | 42 to 42),
// so box.value has type 42. Assigning to number succeeds.
// At runtime, n is "hello" — a string, not a number.
// ============================================================

// FIXME: SKJS should reject — "hello" doesn't extend number
function testUnsound(): void {
  const box = getFirst({ value: "hello" }, { value: 42 });
  const n: number = box.value;
}

// ============================================================
// FIXME: Same unsoundness, reversed argument order
//
// getFirst returns x (first arg), so box = { value: 42 }.
// SKJS infers U = 42 (same narrowing), box.value: 42.
// n = 42 at runtime — happens to be correct, but only by luck:
// the "hello" in the second arg violates the constraint silently.
// ============================================================

// FIXME: SKJS should reject — "hello" doesn't extend number
function testReversedOrder(): void {
  const box = getFirst({ value: 42 }, { value: "hello" });
  const n: number = box.value;
}

// ============================================================
// FIXME: Unsound with three arguments
//
// getFirst returns x = { value: true }. SKJS narrows U to 42 | 100.
// box.value has type 42 | 100 (a number), but runtime value is true.
// ============================================================

// FIXME: SKJS should reject — true doesn't extend number
function testThreeArgs(): void {
  const box = getFirst3({ value: true }, { value: 42 }, { value: 100 });
  const n: number = box.value;
}

function getFirst3<U>(
  x: Constrained<U>,
  y: Constrained<U>,
  z: Constrained<U>,
): Constrained<U> {
  return x;
}

// ============================================================
// Control: both arguments valid — should pass
// ============================================================

function testBothValid(): void {
  const box = getFirst({ value: 42 }, { value: 100 });
  const n: number = box.value;
}
