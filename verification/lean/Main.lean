/-
  verifier -- the trusted verifier for the supported TypeScript fragment.

  Usage: verifier <ast.json> <claims.json> <skjs-file-key>

  Exit 0 accepts the claims; any other exit rejects them. Rejection is the
  only failure mode: the checker never reports a program as accepted on the
  strength of anything SKJS says about itself.
-/
import Verification.Verify
import Verification.JsonDecode

open Verification Lean

/-- Reading a file is the one place the checker can fail for a reason that is
not a rejection; report it as one anyway, so the only exit 0 is an accept. -/
def readOr (path : String) : IO (Except String String) := do
  try
    return .ok (← IO.FS.readFile path)
  catch e =>
    return .error s!"cannot read {path}: {e.toString}"

def run (astPath typeClaimsPath fileKey : String) : IO UInt32 := do
  let astText ← match ← readOr astPath with
    | .ok t => pure t
    | .error e => IO.eprintln s!"reject: {e}"; return 1
  let typeClaimsText ← match ← readOr typeClaimsPath with
    | .ok t => pure t
    | .error e => IO.eprintln s!"reject: {e}"; return 1
  let astJson ← match Json.parse astText with
    | .ok j => pure j
    | .error e => IO.eprintln s!"reject: cannot read the AST: {e}"; return 1
  let typeClaimsJson ← match Json.parse typeClaimsText with
    | .ok j => pure j
    | .error e => IO.eprintln s!"reject: cannot read the claims: {e}"; return 1
  match (do
      let funs ← decodeAst astJson
      let typeClaims ← decodeTypeClaims typeClaimsJson fileKey
      checkFile funs typeClaims) with
  | .ok _ =>
      IO.println s!"accept: {fileKey}"
      return 0
  | .error e =>
      IO.eprintln s!"reject: {fileKey}: {e}"
      return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [astPath, typeClaimsPath, fileKey] => run astPath typeClaimsPath fileKey
  | _ =>
      IO.eprintln "usage: verifier <ast.json> <claims.json> <skjs-file-key>"
      return 2
