/- Produce and independently check evidence for the current calculus and source adapter. -/
import Verification.ExperimentState.RequestCli

open Verification Lean

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--import-skjs-claims", claimsPath, fileKey, digest] =>
      ExperimentState.RequestCli.inspectSourceClaims claimsPath fileKey digest
  | ["--export-source-claims", astPath, claimsPath, fileKey] =>
      ExperimentState.RequestCli.exportSourceClaims astPath claimsPath fileKey
  | ["--check-source-claims", astPath, claimsPath, fileKey, evidencePath] =>
      ExperimentState.RequestCli.sourceFiles astPath claimsPath fileKey evidencePath none true
  | ["--produce-source-claims", astPath, claimsPath, fileKey, evidencePath, depth] =>
      match depth.toNat? with
      | some fuel => ExperimentState.RequestCli.sourceFiles astPath claimsPath fileKey evidencePath (some fuel) true
      | none => IO.eprintln "reject: search depth must be a natural number"; return 2
  | ["--check-stateful-source", astPath, claimsPath, fileKey, evidencePath] =>
      ExperimentState.RequestCli.sourceFiles astPath claimsPath fileKey evidencePath none
  | ["--produce-stateful-source", astPath, claimsPath, fileKey, evidencePath, depth] =>
      match depth.toNat? with
      | some fuel => ExperimentState.RequestCli.sourceFiles astPath claimsPath fileKey evidencePath (some fuel)
      | none => IO.eprintln "reject: search depth must be a natural number"; return 2
  | ["--check-skjs-operations", claimsPath] =>
      ExperimentState.RequestCli.checkOperations claimsPath
  | ["--check-stateful", requestPath, evidencePath] =>
      ExperimentState.RequestCli.checkFiles requestPath evidencePath
  | ["--produce-stateful", requestPath, evidencePath, depth] =>
      match depth.toNat? with
      | some fuel => ExperimentState.RequestCli.produceFile requestPath evidencePath fuel
      | none => IO.eprintln "reject: search depth must be a natural number"; return 2
  | _ =>
      IO.eprintln "usage: verifier --produce-stateful <request.json> <evidence.json> <search-depth>"
      IO.eprintln "       verifier --check-stateful <request.json> <evidence.json>"
      IO.eprintln "       verifier --produce-stateful-source <ast.json> <claims.json> <file-key> <evidence.json> <depth>"
      IO.eprintln "       verifier --check-stateful-source <ast.json> <claims.json> <file-key> <evidence.json>"
      IO.eprintln "       verifier --produce-source-claims <ast.json> <source-claims.json> <file-key> <evidence.json> <depth>"
      IO.eprintln "       verifier --export-source-claims <ast.json> <skjs-claims.json> <file-key>"
      IO.eprintln "       verifier --check-source-claims <ast.json> <source-claims.json> <file-key> <evidence.json>"
      IO.eprintln "       verifier --check-skjs-operations <claims.json>"
      return 2
