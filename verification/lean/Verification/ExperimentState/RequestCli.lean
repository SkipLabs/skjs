import Verification.ExperimentState.SourceClaimExport

/-! File interfaces to raw calculus requests and to the supported source adapter.
Source parsing remains external; source-mode checking reconstructs its request. -/
namespace Verification.ExperimentState.RequestCli
open Lean RequestJson

def readJson (path : String) : IO (Except String Json) := do
  try
    return Json.parse (← IO.FS.readFile path)
  catch e => return .error s!"cannot read {path}: {e}"

def checkFiles (requestPath evidencePath : String) : IO UInt32 := do
  let request ← readJson requestPath
  let evidence ← readJson evidencePath
  let checked := do verifyJson (← request) (← evidence)
  match checked with
  | .ok () => IO.println s!"accept: stateful calculus request {requestPath}"; return 0
  | .error e => IO.eprintln s!"reject: {e}"; return 1

def produceFile (requestPath evidencePath : String) (fuel : Nat) : IO UInt32 := do
  if requestPath == evidencePath then
    IO.eprintln "reject: evidence output must differ from the request file"
    return 1
  let request ← readJson requestPath
  match request.bind (fun j => produceJson j fuel) with
  | .error e => IO.eprintln s!"reject: {e}"; return 1
  | .ok evidence =>
    try
      IO.FS.writeFile evidencePath (evidence.pretty ++ "\n")
      IO.println s!"checked evidence written: {evidencePath}"
      return 0
    catch e => IO.eprintln s!"reject: cannot write {evidencePath}: {e}"; return 1

/-- Conversion writes JSON to stdout; callers decide where to save the two artifacts. -/
def exportSourceClaims (astPath claimsPath fileKey : String) : IO UInt32 := do
  let ast ← readJson astPath
  let claims ← readJson claimsPath
  match (do SourceClaimExport.convert (← ast) (← claims) fileKey) with
  | .ok converted => IO.println converted.compress; return 0
  | .error e => IO.eprintln s!"reject: {e}"; return 1

def sourceFiles (astPath claimsPath fileKey evidencePath : String)
    (fuel : Option Nat) (normalized : Bool := false) : IO UInt32 := do
  if fuel.isSome && (evidencePath == astPath || evidencePath == claimsPath) then
    IO.eprintln "reject: evidence output must differ from the input files"
    return 1
  let ast ← readJson astPath
  let claims ← readJson claimsPath
  match fuel with
  | none =>
    let evidence ← readJson evidencePath
    let checked := do
      let check := if normalized then SourceClaimJson.checkJson else SourceExtraction.checkJson
      check (← ast) (← claims) fileKey (← evidence)
    match checked with
    | .ok () => IO.println s!"accept: stateful source {fileKey}"; return 0
    | .error e => IO.eprintln s!"reject: {e}"; return 1
  | some depth =>
    let produced := do
      let produce := if normalized then SourceClaimJson.produceJson else SourceExtraction.produceJson
      produce (← ast) (← claims) fileKey depth
    match produced with
    | .error e => IO.eprintln s!"reject: {e}"; return 1
    | .ok evidence =>
      try
        IO.FS.writeFile evidencePath (evidence.pretty ++ "\n")
        IO.println s!"checked source evidence written: {evidencePath}"
        return 0
      catch e => IO.eprintln s!"reject: cannot write {evidencePath}: {e}"; return 1

end Verification.ExperimentState.RequestCli
