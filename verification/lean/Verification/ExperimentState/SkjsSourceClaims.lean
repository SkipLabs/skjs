import Verification.ExperimentState.SourceClaims
import Verification.ExperimentState.SourceInput

/-! Decode SKJS type candidates once, before the source compiler consumes them.
The compiler's claim interface itself does not depend on this wire encoding. -/
namespace Verification.ExperimentState.SkjsSourceClaims

def translate (c : SourceInput.Claims) : SourceClaims.Function :=
  let point := fun ty => (SourceInput.translatePoint ty).map (·.type)
  let current := fun ty => (SourceInput.translatePoint ty).toOption.bind (·.current)
  let bindings := fun xs => xs.map fun (name,ty) => (name,point ty)
  ⟨c.name,c.namePos,c.params.map (fun (n,t) => (n,SourceInput.translate t)),SourceInput.translate c.ret,
   c.envs.map (fun (pos,vars) => (pos,bindings vars)),
   c.exprs.map (fun (pos,ty) => (pos,point ty)),
   c.envs.map (fun (pos,vars) => (pos,vars.filterMap fun (n,t) => (current t).map (n,·))),
   c.exprs.filterMap (fun (pos,ty) => (current ty).map (pos,·))⟩

end Verification.ExperimentState.SkjsSourceClaims
