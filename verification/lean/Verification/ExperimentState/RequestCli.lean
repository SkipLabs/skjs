import Verification.ExperimentState.RequestJson

/-! File interface to the versioned calculus protocol. This does not parse
TypeScript or reinterpret SKJS's source-associated claim format. -/
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

end Verification.ExperimentState.RequestCli
