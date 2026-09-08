import Verification.ExperimentState.SourceClaims
import Verification.ExperimentState.SourceInput

/-! Decode SKJS type candidates once, before the source compiler consumes them.
The compiler's claim interface itself does not depend on this wire encoding. -/
namespace Verification.ExperimentState.SkjsSourceClaims

def translate (c : SourceInput.Claims) : SourceClaims.Function :=
  let bindings := fun xs => xs.map fun (name,ty) => (name,SourceInput.translate ty)
  ⟨c.name,c.namePos,bindings c.params,SourceInput.translate c.ret,
   c.envs.map (fun (pos,vars) => (pos,bindings vars)),
   c.exprs.map (fun (pos,ty) => (pos,SourceInput.translate ty))⟩

end Verification.ExperimentState.SkjsSourceClaims
