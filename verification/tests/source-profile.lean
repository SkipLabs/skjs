import Verification.ExperimentState.SourceTypes

/-- The display mirror is compared with this maintained Lean table in undefined.js. -/
def main : IO Unit :=
  IO.println (Lean.toJson Verification.ExperimentState.SourceTypes.types).compress
