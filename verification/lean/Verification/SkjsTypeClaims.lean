import Verification.SourceAst
import Verification.Obligation

namespace Verification

open Core hiding Fn

/-!
Typing claims exported by SKJS for independent verification. The verifier checks
these against the TypeScript source and the calculus's rules. Exporting a claim
does not establish its correctness. Source locations attach claims to AST nodes.
-/

structure FunTypeClaims where
  name : String
  namePos : Span
  params : List (String × Option Ty)
  ret : Option Ty
  /-- Statement start offset ↦ the environment SKJS held on entry. -/
  envs : List (Nat × List (String × Option Ty))
  /-- Expression span ↦ the type SKJS assigned. -/
  exprs : List (Span × Option Ty)

def spanStr (s : Span) : String := s!"[{s.1},{s.2})"

/-! ### Reading the claims -/

def lookupSpan (l : List (Span × Option Ty)) (s : Span) : Option (Option Ty) :=
  match l with
  | [] => none
  | (k, v) :: rest => if k == s then some v else lookupSpan rest s

def lookupEnv (l : List (Nat × List (String × Option Ty))) (n : Nat) :
    Option (List (String × Option Ty)) :=
  match l with
  | [] => none
  | (k, v) :: rest => if k == n then some v else lookupEnv rest n

/-- The type SKJS claimed for the node at `s`. A missing entry means the
claims do not cover the program; an unsupported one means SKJS used a
type outside the supported fragment. Both are rejections. -/
def claimTy (claims : FunTypeClaims) (s : Span) : Except String Ty :=
  match lookupSpan claims.exprs s with
  | none => .error s!"no claimed type for the expression at {spanStr s}"
  | some none => .error s!"the type claimed at {spanStr s} is outside the supported fragment"
  | some (some t) => .ok t

def claimParams : List Param → List (String × Option Ty) → Except String Unit
  | [], [] => .ok ()
  | p :: ps, (n, some t) :: cs =>
      if n == p.name then
        (if Obligation.discharge (.equivalent t p.ty) then claimParams ps cs
         else s!"the claimed type of '{p.name}' differs from its annotation" |> .error)
      else .error "parameter name mismatch"
  | _ :: _, (n, none) :: _ => .error s!"the claimed type of '{n}' is outside the supported fragment"
  | _, _ => .error "the claims declare a different number of parameters"

def claimsBind (f : Fn) (fc : FunTypeClaims) : Except String Unit :=
  if fc.name == f.name && fc.namePos == f.namePos then
    match fc.ret with
    | none => .error "the claimed return type is outside the supported fragment"
    | some t =>
        if Obligation.discharge (.equivalent t f.ret) then claimParams f.params fc.params
        else .error "the claimed return type differs from its annotation"
  else .error "the claims are not bound to this declaration"

end Verification
