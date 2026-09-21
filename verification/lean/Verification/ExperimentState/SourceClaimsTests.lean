import Verification.ExperimentState.SourceExtraction

namespace Verification.ExperimentState.SourceClaimsTests
open Lean SourceExtraction ProgramTyping

private def boolean : Json := Json.mkObj [("top",toJson false),
  ("atoms",toJson [Json.mkObj [("a",toJson "boolean")]])]
private def source : Fragment.Fn :=
  ⟨"identity",(0,1),[⟨"flag",boolean⟩],boolean,
   [.ret (2,5) (.var (3,4) "flag")]⟩
-- These claims have no SKJS type atoms, implicit bindings or function modes.
private def claims : SourceClaims.Function :=
  ⟨"identity",(0,1),[("flag",.ok [1,2])],.ok [1,2],
   [(2,[("flag",.ok [1,2])])],[((3,4),.ok [1,2])],[],[],[]⟩
private def check (c : SourceClaims.Function) : Except String Unit := do
  let r ← extractNormalizedFn SourceTypes.initial source c
  let wire := toJson r.toRequest
  let evidence ← RequestJson.produceJson wire 6 [] [] [] (some r.searchLabels)
  RequestJson.verifyJson wire evidence
private def ok (x : Except String α) : Bool := match x with | .ok _ => true | .error _ => false
#guard ok (check claims)
#guard !ok (check { claims with envs := [(2,[("flag",.ok [2])])] })
#guard !ok (check { claims with params := [("flag",.ok [2])] })
#guard !ok (check { claims with ret := .ok [2] })
#guard !ok (check { claims with exprs := [((3,4),.ok [2])] })
#guard !ok (check { claims with exprs := [((3,4),.ok [4])] })
#guard !ok (check { claims with envs := [] })
#guard !ok (check { claims with envs := [(2,[("flag",.ok [1,2]),("flag",.ok [1,2])])] })
#guard !ok (check { claims with exprs := [((3,4),.error "unsupported producer type")] })
-- Unrelated export bindings may be unavailable, but cannot supply a local type.
#guard ok (check { claims with envs := [(2,[("flag",.ok [1,2]),("this",.error "unsupported")])] })
#guard !ok (check { claims with envs := [(2,[("flag",.error "unsupported")])] })

-- Existing evidence cannot justify a different normalized environment or type.
private def checkAgainst (c : SourceClaims.Function) : Except String Unit := do
  let original ← extractNormalizedFn SourceTypes.initial source claims
  let evidence ← RequestJson.produceJson (toJson original.toRequest) 6 [] [] [] (some original.searchLabels)
  let changed ← extractNormalizedFn SourceTypes.initial source c
  RequestJson.verifyJson (toJson changed.toRequest) evidence
#guard !ok (checkAgainst { claims with envs := [(2,[("flag",.ok [2])])] })
#guard !ok (checkAgainst { claims with exprs := [((3,4),.ok [2])] })

private def skjs : Fragment.Claims :=
  ⟨"identity",(0,1),[("flag",boolean)],boolean,
   [(2,[("flag",boolean)])],[((3,4),boolean)]⟩
#guard ((extractFn source skjs).map (fun r => toJson r.toRequest)).toOption ==
  ((extractNormalizedFn SourceTypes.initial source claims).map (fun r => toJson r.toRequest)).toOption

end Verification.ExperimentState.SourceClaimsTests
