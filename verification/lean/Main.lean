/- Produce and independently check evidence for the current calculus and source adapter. -/
import Verification.Model.Source.RequestCli

open Verification Lean

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--import-skjs-claims", claimsPath, fileKey, digest] =>
      Model.RequestCli.inspectSourceClaims claimsPath fileKey digest
  | ["--export-source-claims", astPath, claimsPath, fileKey] =>
      Model.RequestCli.exportSourceClaims astPath claimsPath fileKey
  | ["--check-source-claims", astPath, claimsPath, fileKey, evidencePath] =>
      Model.RequestCli.sourceFiles astPath claimsPath fileKey evidencePath none true
  | ["--produce-source-claims", astPath, claimsPath, fileKey, evidencePath, depth] =>
      match depth.toNat? with
      | some fuel => Model.RequestCli.sourceFiles astPath claimsPath fileKey evidencePath (some fuel) true
      | none => IO.eprintln "reject: search depth must be a natural number"; return 2
  | ["--check-stateful-source", astPath, claimsPath, fileKey, evidencePath] =>
      Model.RequestCli.sourceFiles astPath claimsPath fileKey evidencePath none
  | ["--produce-stateful-source", astPath, claimsPath, fileKey, evidencePath, depth] =>
      match depth.toNat? with
      | some fuel => Model.RequestCli.sourceFiles astPath claimsPath fileKey evidencePath (some fuel)
      | none => IO.eprintln "reject: search depth must be a natural number"; return 2
  -- One function of the file, the others its module: for reports that locate
  -- each function's own result.
  | ["--check-source-claims", astPath, claimsPath, fileKey, evidencePath, "--function", name, start, stop] =>
      match start.toNat?, stop.toNat? with
      | some a, some b => Model.RequestCli.sourceFiles astPath claimsPath fileKey evidencePath none true (some (name, (a, b)))
      | _, _ => IO.eprintln "reject: a function position is two natural numbers"; return 2
  | ["--produce-source-claims", astPath, claimsPath, fileKey, evidencePath, depth, "--function", name, start, stop] =>
      match depth.toNat?, start.toNat?, stop.toNat? with
      | some fuel, some a, some b => Model.RequestCli.sourceFiles astPath claimsPath fileKey evidencePath (some fuel) true (some (name, (a, b)))
      | _, _, _ => IO.eprintln "reject: search depth and function position must be natural numbers"; return 2
  | ["--check-stateful-source", astPath, claimsPath, fileKey, evidencePath, "--function", name, start, stop] =>
      match start.toNat?, stop.toNat? with
      | some a, some b => Model.RequestCli.sourceFiles astPath claimsPath fileKey evidencePath none false (some (name, (a, b)))
      | _, _ => IO.eprintln "reject: a function position is two natural numbers"; return 2
  | ["--produce-stateful-source", astPath, claimsPath, fileKey, evidencePath, depth, "--function", name, start, stop] =>
      match depth.toNat?, start.toNat?, stop.toNat? with
      | some fuel, some a, some b => Model.RequestCli.sourceFiles astPath claimsPath fileKey evidencePath (some fuel) false (some (name, (a, b)))
      | _, _, _ => IO.eprintln "reject: search depth and function position must be natural numbers"; return 2
  | ["--check-skjs-operations", claimsPath] =>
      Model.RequestCli.checkOperations claimsPath
  | ["--check-stateful", requestPath, evidencePath] =>
      Model.RequestCli.checkFiles requestPath evidencePath
  | ["--produce-stateful", requestPath, evidencePath, depth] =>
      match depth.toNat? with
      | some fuel => Model.RequestCli.produceFile requestPath evidencePath fuel
      | none => IO.eprintln "reject: search depth must be a natural number"; return 2
  | _ =>
      IO.eprintln "usage: verifier --produce-stateful <request.json> <evidence.json> <search-depth>"
      IO.eprintln "       verifier --check-stateful <request.json> <evidence.json>"
      IO.eprintln "       verifier --produce-stateful-source <ast.json> <claims.json> <file-key> <evidence.json> <depth>"
      IO.eprintln "       verifier --check-stateful-source <ast.json> <claims.json> <file-key> <evidence.json>"
      IO.eprintln "       verifier --produce-source-claims <ast.json> <source-claims.json> <file-key> <evidence.json> <depth>"
      IO.eprintln "       verifier --export-source-claims <ast.json> <skjs-claims.json> <file-key>"
      IO.eprintln "       verifier --check-source-claims <ast.json> <source-claims.json> <file-key> <evidence.json>"
      IO.eprintln "       (each source mode also takes --function <name> <start> <end>: one function, the others its module)"
      IO.eprintln "       verifier --check-skjs-operations <claims.json>"
      return 2
