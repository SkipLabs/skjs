import Verification.Calculus.Typing

/-!
Pins `Calculus/Typing.lean`: that `NodeOk`, `FnOk` and `ProgOk` are
inhabitable.

Not in the trusted base, but this file guards against a specific kind of
vacuity. `Core.sound` reads `ProgOk p → …`. If the rules admitted no
derivation -- one rule with an unsatisfiable side condition would do it --
`sound` would remain a theorem and say nothing. The derivation below is the
witness that it says something.

What belongs here: derivations built by hand against the rules, not obtained
from the checker and not routed through `Lowering`. `Tests/Verify.lean` covers
the decision procedure and `Tests/Lowering.lean` the translation; this file
covers the rules themselves, so its graph is written out directly.

The graph chosen has a real join: node 2 is reached both from node 1 and from
node 0's false edge, so the environment assigned to it has to be justified
twice. That is the case the block judgement could not state.

Not yet covered: derivations using `call`, `&&`/`||`, and `Node.jump`.
-/

namespace Verification
namespace Tests

open Core

private def boolT : Ty := ofAtom .bool
private def strT : Ty := ofAtom .str

/--
    if (b) { const y = "a"; }
    return "z";
-/
private def g : Core.Fn :=
  { name := "g", params := [("b", boolT)], ret := strT
    code := [ .branch (.var "b") (some 1) (some 2)
            , .set "y" (.lit (.vstr "a")) (some 2)
            , .ret (.lit (.vstr "z")) ] }

private def prog : Core.Prog := [g]

/-- One environment per node. The branch establishes a fact about `b` that
neither successor needs, and the binding node 1 makes is forgotten at the
merge -- forgetting is what `Covers` permits. -/
private def envs : List TEnv := [[("b", boolT)], [("b", boolT)], [("b", boolT)]]

/-- A decidable form of the one edge obligation these nodes need: `b` must be
supplied at a type contained in `boolT`. The narrowed environments on the
branch edges give it `true`/`false` literal types, so this is genuinely a
subtyping check, not an equality. -/
private def suppliesB (G : TEnv) : Bool :=
  match tenvGet G "b" with
  | some s => sub s boolT
  | none => false

private theorem covers_b {G : TEnv} (h : suppliesB G = true) :
    Covers G [("b", boolT)] := by
  refine Covers_of_sub ?_
  intro x t hx
  by_cases hb : x = "b"
  · subst hb
    simp only [tenvGet, BEq.rfl, if_true, Option.some.injEq] at hx
    subst hx
    rw [suppliesB] at h
    split at h
    · exact ⟨_, by assumption, h⟩
    · exact absurd h (by simp)
  · exfalso; simp [tenvGet] at hx; exact hb hx.1.symm

private theorem edge_to (k : Nat) (hk : envs[k]? = some [("b", boolT)])
    {G : TEnv} (h : suppliesB G = true) : Edge g envs G (some k) :=
  ⟨[("b", boolT)], hk, covers_b h⟩

theorem prog_ok : Core.ProgOk prog := by
  intro f hf
  simp only [prog, List.mem_singleton] at hf
  subst hf
  refine ⟨envs, ?_, ?_, ?_⟩
  · exact edge_to 0 rfl (by decide)
  · intro pc G h
    match pc with
    | 0 => exact ⟨_, rfl⟩
    | 1 => exact ⟨_, rfl⟩
    | 2 => exact ⟨_, rfl⟩
    | (n + 3) => simp [envs] at h
  · intro pc G node hpc hnode
    match pc with
    | 0 =>
      cases hpc; cases hnode
      exact .branch (.var (t0 := boolT) (by decide) (by decide))
        (edge_to 1 rfl (by decide)) (edge_to 2 rfl (by decide))
    | 1 =>
      cases hpc; cases hnode
      exact .set (t := ofAtom (.strLit "a")) (.lit (by decide))
        (edge_to 2 rfl (by decide))
    | 2 =>
      cases hpc; cases hnode
      exact .ret (.lit (by decide))
    | (n + 3) => simp [envs] at hpc

end Tests
end Verification
