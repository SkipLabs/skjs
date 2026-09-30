import Verification.Model.Types.EquationSubstitution
import Verification.Model.Types.PositiveCertificates

/-! Recursive equation instances use the ordinary subtyping proof checker.
Only the image-table validator changes; its semantic law is proved, and every
bound, signature, receiver, effect and argument-pack check remains shared. -/
namespace Verification.Model.EquationGraphs
open PositiveGraphs PositiveRules PositiveCertificates

/-- Each recorded image equals structural substitution of its equation label. -/
def Equations.instanceImageCheck (equations : Equations) : InstanceImageCheck equations.graph where
  compare := fun _ c => ComparisonResult.fromBool (substitutionTableOk c.table)
  sound := fun bs c hlen hkinds checked η =>
    equations.substitutionTable_instanceImages η bs c.instances c.table hlen hkinds (by simpa only [ComparisonResult.accepted_fromBool] using checked)

end Verification.Model.EquationGraphs
