import Verification.ExperimentState.SourceExtraction

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

def sourceFiles (astPath claimsPath fileKey evidencePath : String)
    (fuel : Option Nat) : IO UInt32 := do
  if fuel.isSome && (evidencePath == astPath || evidencePath == claimsPath) then
    IO.eprintln "reject: evidence output must differ from the input files"
    return 1
  let ast ← readJson astPath
  let claims ← readJson claimsPath
  match fuel with
  | none =>
    let evidence ← readJson evidencePath
    let checked := do SourceExtraction.checkJson (← ast) (← claims) fileKey (← evidence)
    match checked with
    | .ok () => IO.println s!"accept: stateful source {fileKey}"; return 0
    | .error e => IO.eprintln s!"reject: {e}"; return 1
  | some depth =>
    let produced := do SourceExtraction.produceJson (← ast) (← claims) fileKey depth
    match produced with
    | .error e => IO.eprintln s!"reject: {e}"; return 1
    | .ok evidence =>
      try
        IO.FS.writeFile evidencePath (evidence.pretty ++ "\n")
        IO.println s!"checked source evidence written: {evidencePath}"
        return 0
      catch e => IO.eprintln s!"reject: cannot write {evidencePath}: {e}"; return 1

end Verification.ExperimentState.RequestCli
