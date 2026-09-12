import Verification.ExperimentState.CallableObjects
import Verification.ExperimentState.ProgramTyping
/-!
# Function objects: the operational slice

What the language layer says about `obj l (.lam b)` and `attach`, checked on
concrete terms: creation allocates the bag and yields a fresh identity, a call
is one beta step, reads and writes go to the bag, the shape test answers as
for a function, and evaluation stays deterministic. A plain object is the same
constructor carrying no closure. Semantic regressions also check overloaded
calls, writable bags, fresh allocation and rejection of unsafe code.
-/
namespace Verification.ExperimentState.CallableTests

/-- Creating a function object allocates its bag: the closure is paired with the new location. -/
example : Step [] (.attach (.lam (.var 0)) .tru) [.tru] (.obj 0 (.lam (.var 0))) :=
  .attachV rfl

/-- Calling it is one beta step, as for a lambda; the heap is untouched. -/
example : Step [.tru] (.app (.obj 0 (.lam (.var 0))) .fls) [.tru] .fls :=
  .betaC rfl

/-- Reading an object reads its bag, whether or not it carries a closure. -/
example : Step [.tru] (.read (.obj 0 (.lam (.var 0)))) [.tru] .tru := .readV rfl
example : Step [.tru] (.read (.obj 0 .nul)) [.tru] .tru := .readV rfl

/-- Writing writes the bag, and the code is unchanged. -/
example : Step [.tru] (.write (.obj 0 (.lam (.var 0))) .fls) [.fls] .nul :=
  .writeV rfl (by decide)

/-- Two values with one identity share the bag: a write through one is read through the other. -/
example : Step [.tru] (.write (.obj 0 (.lam (.var 0))) .fls) [.fls] .nul ∧
    Step [.fls] (.read (.obj 0 (.lam (.var 0)))) [.fls] .fls :=
  ⟨.writeV rfl (by decide), .readV rfl⟩

/-- `typeof` says function for one and object for the other; the tests stay total. -/
example : tagHolds .isFun (.obj 0 (.lam (.var 0))) = true := rfl
example : tagHolds .isRef (.obj 0 (.lam (.var 0))) = false := rfl
example : tagHolds .isRef (.obj 0 .nul) = true := rfl
example : tagHolds .isFun (.obj 0 .nul) = false := rfl

/-- Only a closure or nothing may sit in the slot; anything else is not a value. -/
example : isVal (.obj 0 .tru) = false := rfl

/-- The only step out of a creation is the allocation. -/
example {h' t} (hs : Step [.nul] (.attach (.lam .nul) .tru) h' t) :
    h' = [.nul, .tru] ∧ t = .obj 1 (.lam .nul) :=
  attach_step_inv rfl hs

/-- Substitution reaches the code and leaves the identity alone. -/
example : subst 0 .tru (.obj 3 (.lam (.app (.var 1) (.var 0)))) =
    .obj 3 (.lam (.app .tru (.var 0))) := by
  simp [subst]

/-- A function object whose code is closed under one binder is a closed value. -/
example : Scoped 0 (.obj 7 (.lam (.var 0))) := by simp [Scoped]
example : ¬ Scoped 0 (.obj 7 (.lam (.var 1))) := by simp [Scoped]

/-- Identity code satisfies two distinct signatures on one writable object. -/
def signatures : List (Fam × Fam) := [(boolT, boolT), (nulT, nulT)]

theorem identity_arrow (A : Fam) (hA : ValOnly A) (n W) :
    arrowT A A n W (.lam (.var 0)) := by
  apply lam_intro _ _ _ (by simp [Scoped])
  intro j hj U hx hu heap hh a ha
  simpa [subst] using value_safe A j U heap a (hA _ _ _ ha) ha

theorem identity_overloaded (n W) : arrowsT signatures n W (.lam (.var 0)) := by
  apply arrowsT_of_all rfl (by simp [Scoped])
  intro p hp
  simp only [signatures, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact identity_arrow boolT boolT_valOnly n W
  · exact identity_arrow nulT nulT_valOnly n W

theorem identity_object (n : Nat) :
    callableT signatures boolT n (ofList [res boolT]) (.obj 0 (.lam (.var 0))) :=
  ⟨⟨0, .lam (.var 0), rfl, rfl, ref_param_inhabited boolT n⟩,
    (arrowsT_object_iff signatures 0 (.var 0) n _).mpr (identity_overloaded n _)⟩

/-- Allocation is safe at every budget, including when its result is observed. -/
theorem identity_creation (n W h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (callableT signatures boolT) n W h (.attach (.lam (.var 0)) .tru) :=
  attach_rule boolT_adm n W h _ _ (identity_overloaded n W) rfl hw hh (Or.inl rfl)

/-- The same object supports its call contract, its bag read, and its bag write. -/
theorem identity_operations (n : Nat) (h : Heap)
    (hw : WorldAdm (ofList [res boolT] : WorldT n))
    (hh : HeapOk n (ofList [res boolT]) h) :
    Safe boolT n (ofList [res boolT]) h (.app (.obj 0 (.lam (.var 0))) .fls) ∧
    Safe boolT n (ofList [res boolT]) h (.read (.obj 0 (.lam (.var 0)))) ∧
    Safe nulT n (ofList [res boolT]) h (.write (.obj 0 (.lam (.var 0))) .fls) := by
  have hf : arrowT boolT boolT n (ofList [res boolT]) (.obj 0 (.lam (.var 0))) :=
    ⟨(identity_object n).2.1, (identity_object n).2.2 (boolT, boolT) (by simp [signatures])⟩
  exact ⟨app_elim boolT_adm boolT_valOnly hf (Or.inr rfl) hw hh,
    bag_read boolT_valOnly (identity_object n).1 hw hh,
    bag_write boolT_adm (identity_object n).1 (Or.inr rfl) rfl hw hh⟩

/-- Shape alone does not justify a signature whose body gets stuck. -/
theorem stuck_object_excluded :
    ¬ arrowT nulT nulT 2 (ofList []) (.obj 0 (.lam (.app .nul .nul))) := by
  intro hf
  have hs := hf.2 1 (by decide) (ofList [])
    (by simpa [trunc, toList_ofList] using WExt_refl (ofList [] : WorldT 1))
    (by intro l c hl; simp [lookup] at hl) [] (by simp [HeapOk, lookup]) .nul rfl
  exact stuck_not_safe nulT 0 (ofList []) [] hs

/-- The legacy reference type remains the plain-object view. -/
example (n W) : ¬ refT boolT n W (.obj 0 (.lam (.var 0))) := by
  rintro ⟨l, c, he, _⟩; cases he

/-- Function-shape refinement recognizes the new inhabitants of arrows. -/
example : PositiveNormalization.valueShape (.obj 0 (.lam (.var 0))) =
    PositiveNormalization.shape (α := Nat) (.arrs []) := rfl

#print axioms identity_creation
#print axioms identity_operations
#print axioms stuck_object_excluded

#print axioms Step_det

end Verification.ExperimentState.CallableTests
