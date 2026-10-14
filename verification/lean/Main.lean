/- Produce and independently check evidence for source claims. -/
import Verification.Source.RequestCli

open Verification Lean

def main (args : List String) : IO UInt32 := do
  -- `--trace-subtyping FILE` first: the subtyping questions the run asks,
  -- one JSON line each (`SubtypingTrace`); the run is otherwise the same.
  let args ← match args with
    | "--trace-subtyping" :: path :: rest => do
      Verification.SubtypingTrace.open_ path
      pure rest
    | _ => pure args
  let (budget, args) ← match args with
    | "--subtype-rounds" :: rounds :: rest => do
      match rounds.toNat? with
      | some n => pure (({ rounds := n } : Verification.PositiveCertificates.SearchBudget), rest)
      | none => IO.eprintln "reject: subtype rounds must be a natural number"; return 2
    | _ => pure ({}, args)
  match args with
  | ["--lower-control-flow", astPath] =>
      Verification.RequestCli.flowFile astPath
  | ["--lower-program", astPath, claimsPath, fileKey] =>
      Verification.RequestCli.lowerFile astPath claimsPath fileKey
  | ["--check-source-claims", astPath, claimsPath, fileKey, evidencePath] =>
      Verification.RequestCli.sourceFiles astPath claimsPath fileKey evidencePath none none budget
  | ["--produce-source-claims", astPath, claimsPath, fileKey, evidencePath, depth] =>
      match depth.toNat? with
      | some fuel => Verification.RequestCli.sourceFiles astPath claimsPath fileKey evidencePath (some fuel) none budget
      | none => IO.eprintln "reject: search depth must be a natural number"; return 2
  -- One function of the file, the others its module: for reports that locate
  -- each function's own result.
  | ["--check-source-claims", astPath, claimsPath, fileKey, evidencePath, "--function", name, start, stop] =>
      match start.toNat?, stop.toNat? with
      | some a, some b => Verification.RequestCli.sourceFiles astPath claimsPath fileKey evidencePath none (some (name, (a, b))) budget
      | _, _ => IO.eprintln "reject: a function position is two natural numbers"; return 2
  | ["--produce-source-claims", astPath, claimsPath, fileKey, evidencePath, depth, "--function", name, start, stop] =>
      match depth.toNat?, start.toNat?, stop.toNat? with
      | some fuel, some a, some b => Verification.RequestCli.sourceFiles astPath claimsPath fileKey evidencePath (some fuel) (some (name, (a, b))) budget
      | _, _, _ => IO.eprintln "reject: search depth and function position must be natural numbers"; return 2
  | _ =>
      IO.eprintln "usage: verifier --lower-control-flow <ast.json>"
      IO.eprintln "       verifier --lower-program <ast.json> <source-claims.json> <file-key>"
      IO.eprintln "       verifier --produce-source-claims <ast.json> <source-claims.json> <file-key> <evidence.json> <depth>"
      IO.eprintln "       verifier --check-source-claims <ast.json> <source-claims.json> <file-key> <evidence.json>"
      IO.eprintln "       (each mode also takes --function <name> <start> <end>: one function, the others its module)"
      IO.eprintln "       (any mode may be preceded by --trace-subtyping <file> and --subtype-rounds <rounds>)"
      return 2
