import Verification.Model.Types.EquationSubstitution
import Verification.Model.Types.PositiveCertificates

/-! Recursive equation instances use the ordinary subtyping proof checker.
Only the image-table validator changes; its semantic law is proved, and every
bound, signature, receiver, effect and argument-pack check remains shared. -/
namespace Verification.Model.EquationGraphs
open PositiveGraphs PositiveRules PositiveCertificates

/-- Computed structural images replace finite row closure for instantiation.
The old domain/free fields are not needed for this check; other proof forms
still check any domain and free-support evidence they consume. -/
def Equations.instanceImageCheck (equations : Equations) : InstanceImageCheck equations.graph where
  check := fun _ c => substitutionTableOk c.table
  sound := fun bs c hlen hkinds checked η =>
    equations.substitutionTable_instanceImages η bs c.instances c.table hlen hkinds checked

/-- The same proof language and traversal, using complete recursive equations
for instance images. Equation lowering checks supplied subtype proofs with it. -/
def Equations.checkSubtype (equations : Equations)
    (S T : List (Label equations.signature)) (proof : SubtypeChoices (Label equations.signature)) : Bool :=
  checkUsing equations.graph equations.instanceImageCheck S T proof

theorem Equations.checkSubtype_sound (equations : Equations)
    {S T : List (Label equations.signature)} {proof : SubtypeChoices (Label equations.signature)}
    (checked : equations.checkSubtype S T proof = true) :
    ∀ η, FamLe (mixedMeaning equations.graph η S) (mixedMeaning equations.graph η T) :=
  checkUsing_sound checked

#print axioms Equations.checkSubtype_sound

end Verification.Model.EquationGraphs
