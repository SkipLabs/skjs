import Verification.Calculus

namespace Verification

open Core

/-- A type relation to establish. Source annotations set the required types;
SKJS supplies claimed intermediate types. Neither is evidence for a relation.
File names, spans and missing entries are handled by input validation. -/
inductive Obligation where
  | subtype (actual required : Ty)
  | equivalent (claimed declared : Ty)

namespace Obligation

/-- What an obligation means, independently of the procedure used to solve it. -/
def Holds : Obligation → Prop
  | .subtype a b => ∀ v, mem v a → mem v b
  | .equivalent a b => ∀ v, mem v a ↔ mem v b

/-- F0 needs only the calculus's finite type comparisons. Later fragments may
check supplied derivations here; supplied evidence must still be verified. -/
def discharge : Obligation → Bool
  | .subtype a b => sub a b
  | .equivalent a b => equiv a b

theorem discharge_sound {o : Obligation} (h : o.discharge = true) : o.Holds := by
  cases o with
  | subtype a b => exact fun _ hv => sub_sound h hv
  | equivalent a b =>
    have hs : sub a b = true ∧ sub b a = true := by
      simpa [discharge, equiv] using h
    obtain ⟨hab, hba⟩ := hs
    exact fun _ => ⟨fun hv => sub_sound hab hv, fun hv => sub_sound hba hv⟩

-- A claimed branch type must cover incoming values AND fit the return type.
-- `never` fails the former; `unknown` fails the latter.
#guard discharge (.subtype (ofAtom .str) (ofAtom .str))
#guard !discharge (.subtype (ofAtom .str) never)
#guard !discharge (.subtype unknown (ofAtom .str))
#guard !discharge (.equivalent unknown (ofAtom .str))

end Obligation
end Verification
