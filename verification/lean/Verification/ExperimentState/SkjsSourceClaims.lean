import Verification.ExperimentState.SourceClaims
import Verification.ExperimentState.Fragment

/-! Decode SKJS type candidates once, before the source compiler consumes them.
The compiler's claim interface itself does not depend on this wire encoding.
Every candidate is attempted on its own: a rejected one is kept as its failure
and leaves no rows in the table. -/
namespace Verification.ExperimentState.SkjsSourceClaims
open SourceTypes

def translate (c : Fragment.Claims) : Lowering SourceClaims.Function := do
  let candidate := fun ty => attempt (Fragment.translate ty)
  let point := fun ty => attempt (Fragment.translatePoint ty)
  let params ← c.params.mapM fun (name,ty) => do return (name, ← candidate ty)
  let ret ← candidate c.ret
  let envs ← c.envs.mapM fun (pos,vars) => do
    return (pos, ← vars.mapM fun (name,ty) => do return (name, ← point ty))
  let exprs ← c.exprs.mapM fun (pos,ty) => do return (pos, ← point ty)
  let current := fun (p : Except String Fragment.PointType) => p.toOption.bind (·.current)
  return ⟨c.name,c.namePos,params,ret,
    envs.map (fun (pos,vars) => (pos, vars.map fun (name,p) => (name, p.map (·.type)))),
    exprs.map (fun (pos,p) => (pos, p.map (·.type))),
    envs.map (fun (pos,vars) => (pos, vars.filterMap fun (name,p) => (current p).map (name,·))),
    exprs.filterMap (fun (pos,p) => (current p).map (pos,·))⟩

end Verification.ExperimentState.SkjsSourceClaims
