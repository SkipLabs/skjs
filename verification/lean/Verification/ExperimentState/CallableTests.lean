import Verification.ExperimentState.CallableObjects
import Verification.ExperimentState.ProgramTyping
/-!
# Function objects: the operational slice

What the language layer says about `obj l (.closure 1 b)` and `make`, checked on
concrete terms: creation allocates the bag and yields a fresh identity, a call
is one beta step, reads and writes go to the bag, the shape test answers as
for a function, and evaluation stays deterministic. A plain object is the same
constructor carrying no closure. Semantic regressions also check overloaded
calls, writable bags, fresh allocation and rejection of unsafe code.
-/
namespace Verification.ExperimentState.CallableTests

/-- Creating a function object allocates its bag: the closure is paired with the new location. -/
example : Step [] (.attach (.var 0) .tru) [.tru] (.obj 0 (.closure 1 (.var 0))) :=
  .makeV rfl

/-- Creating the same source function twice produces distinct identities. -/
example : Step [] (.funE (.var 0)) [.nul] (.fn 0 (.var 0)) ∧
    Step [.nul] (.funE (.var 0)) [.nul,.nul] (.fn 1 (.var 0)) :=
  ⟨.makeV rfl, .makeV rfl⟩

/-- Code is not evaluated during creation, even if invoking it would get stuck. -/
example : Step [] (.funE (.app .nul .nul)) [.nul] (.fn 0 (.app .nul .nul)) :=
  .makeV rfl

/-- An allocating initializer gets its identity first, for any pair of descriptors.
The outer allocation uses the updated heap length and stores that exact object. -/
example (inner outer : CallCode) :
    Step [] (.make outer (.make inner .tru)) [.tru] (.make outer (.obj 0 inner)) ∧
    Step [.tru] (.make outer (.obj 0 inner)) [.tru, .obj 0 inner] (.obj 1 outer) :=
  ⟨.makeC (.makeV rfl), .makeV rfl⟩

/-- Plain and callable objects draw fresh identities from the same heap. -/
example : Step [] (.alloc .tru) [.tru] (.obj 0 .absent) ∧
    Step [.tru] (.funE (.var 0)) [.tru, .nul] (.fn 1 (.var 0)) ∧
    Step [.tru, .nul] (.alloc .fls) [.tru, .nul, .fls] (.obj 2 .absent) :=
  ⟨.makeV rfl, .makeV rfl, .makeV rfl⟩

/-- Creating an object cannot hide a stuck initializer, regardless of its descriptor. -/
example (code : CallCode) {h h' t} : ¬ Step h (.make code (.app .nul .nul)) h' t := by
  intro hs
  cases hs with
  | makeArg hg _ hs =>
    obtain ⟨rfl, rfl⟩ := singleton_get hg
    exact stuck_no_step hs
  | makeFields hv _ => simpa [isVal] using hv (.app .nul .nul) (by simp)

/-- Calling it is one beta step; the heap is untouched. -/
example : Step [.tru] (.app (.obj 0 (.closure 1 (.var 0))) .fls) [.tru] .fls :=
  .beta rfl

/-- Reading an object reads its bag, whether or not it carries a closure. -/
example : Step [.tru] (.read (.obj 0 (.closure 1 (.var 0)))) [.tru] .tru := .readV rfl
example : Step [.tru] (.read (.obj 0 .absent)) [.tru] .tru := .readV rfl

/-- Writing writes the bag, and the code is unchanged. -/
example : Step [.tru] (.write (.obj 0 (.closure 1 (.var 0))) .fls) [.fls] .nul :=
  .writeV rfl (by decide)

/-- Two values with one identity share the bag: a write through one is read through the other. -/
example : Step [.tru] (.write (.obj 0 (.closure 1 (.var 0))) .fls) [.fls] .nul ∧
    Step [.fls] (.read (.obj 0 (.closure 1 (.var 0)))) [.fls] .fls :=
  ⟨.writeV rfl (by decide), .readV rfl⟩

/-- `typeof` says function for one and object for the other; the tests stay total. -/
example : tagHolds .isFun (.obj 0 (.closure 1 (.var 0))) = true := rfl
example : tagHolds .isRef (.obj 0 (.closure 1 (.var 0))) = false := rfl
example : tagHolds .isRef (.obj 0 .absent) = true := rfl
example : tagHolds .isFun (.obj 0 .absent) = false := rfl

/-- Function creation is a computation, even when its body is closed. -/
example : isVal (.funE (.var 0)) = false := rfl

/-- The only step out of a creation is the allocation. -/
example {h' t} (hs : Step [.nul] (.attach .nul .tru) h' t) :
    h' = [.nul, .tru] ∧ t = .obj 1 (.closure 1 .nul) :=
  make_step_inv rfl hs

/-- Substitution reaches the code and leaves the identity alone. -/
example : subst 0 .tru (.obj 3 (.closure 1 (.app (.var 1) (.var 0)))) =
    .obj 3 (.closure 1 (.app .tru (.var 0))) := by
  simp [subst]

/-- A function object whose code is closed under one binder is a closed value. -/
example : Scoped 0 (.obj 7 (.closure 1 (.var 0))) := by simp [Scoped]
example : ¬ Scoped 0 (.obj 7 (.closure 1 (.var 1))) := by simp [Scoped]

/-- Identity code satisfies two distinct signatures on one writable object. -/
def signatures : List (Fam × Fam) := [(boolT, boolT), (nulT, nulT)]

theorem identity_arrow (A : Fam) (hA : ValOnly A) (n W) :
    arrowT A A n W (.fn 0 (.var 0)) := by
  apply fn_intro _ _ _ (by simp [Scoped])
  intro j hj U hx hu heap hh a ha
  simpa [subst] using value_safe A j U heap a (hA _ _ _ ha) ha

theorem identity_overloaded (n W) : CodeSpec signatures n W (.var 0) := by
  apply (arrowsT_code_iff signatures [(valueField, 0)] (.var 0) n W).mp
  apply arrowsT_of_all rfl (by simp [Scoped])
  intro p hp
  simp only [signatures, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact identity_arrow boolT boolT_valOnly n W
  · exact identity_arrow nulT nulT_valOnly n W

theorem identity_object (n : Nat) :
    callableT signatures [(valueField, boolT)] n (ofList [res boolT]) (.obj 0 (.closure 1 (.var 0))) :=
  ⟨⟨_, .closure 1 (.var 0), rfl, rfl, ref_param_inhabited boolT n⟩,
    (arrowsT_code_iff signatures [(valueField, 0)] (.var 0) n _).mpr (identity_overloaded n _)⟩

/-- Allocation is safe at every budget, including when its result is observed. -/
theorem identity_creation (n W h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (callableT signatures [(valueField, boolT)]) n W h (.attach (.var 0) .tru) :=
  attach_rule boolT_adm n W h _ _ (identity_overloaded n W) rfl hw hh (Or.inl rfl)

/-- The same object supports its call contract, its bag read, and its bag write. -/
theorem identity_operations (n : Nat) (h : Heap)
    (hw : WorldAdm (ofList [res boolT] : WorldT n))
    (hh : HeapOk n (ofList [res boolT]) h) :
    Safe boolT n (ofList [res boolT]) h (.app (.obj 0 (.closure 1 (.var 0))) .fls) ∧
    Safe boolT n (ofList [res boolT]) h (.read (.obj 0 (.closure 1 (.var 0)))) ∧
    Safe nulT n (ofList [res boolT]) h (.write (.obj 0 (.closure 1 (.var 0))) .fls) := by
  have hf : arrowT boolT boolT n (ofList [res boolT]) (.obj 0 (.closure 1 (.var 0))) :=
    ⟨(identity_object n).2.1, (identity_object n).2.2 (boolT, boolT) (by simp [signatures])⟩
  exact ⟨app_elim boolT_adm boolT_valOnly hf (Or.inr rfl) hw hh,
    bag_read boolT_valOnly (by simp) (identity_object n).1 hw hh,
    bag_write boolT_adm (by simp) (identity_object n).1 (Or.inr rfl) rfl hw hh⟩

/-- Shape alone does not justify a signature whose body gets stuck. -/
theorem stuck_object_excluded :
    ¬ arrowT nulT nulT 2 (ofList []) (.obj 0 (.closure 1 (.app .nul .nul))) := by
  intro hf
  have hs := hf.2 1 (by decide) (ofList [])
    (by simpa [trunc, toList_ofList] using WExt_refl (ofList [] : WorldT 1))
    (by intro l c hl; simp [lookup] at hl) [] (by simp [HeapOk, lookup]) .nul rfl
  exact stuck_not_safe nulT 0 (ofList []) [] hs

/-- The legacy reference type remains the plain-object view. -/
example (n W) : ¬ refT boolT n W (.obj 0 (.closure 1 (.var 0))) := by
  rintro ⟨flds, he, _⟩; cases he

/-- Function-shape refinement recognizes the new inhabitants of arrows. -/
example : PositiveNormalization.valueShape (.obj 0 (.closure 1 (.var 0))) =
    PositiveNormalization.shape (α := Nat) (.arrs []) := rfl

#print axioms identity_creation
#print axioms identity_operations
#print axioms stuck_object_excluded

#print axioms Step_det

end Verification.ExperimentState.CallableTests
