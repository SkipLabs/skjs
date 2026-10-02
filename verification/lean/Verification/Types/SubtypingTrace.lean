import Lean.Data.Json

/-! Tracing the subtyping algorithm (`verifier --trace-subtyping FILE`).

Each hook here is, logically, the identity on its result: `question k s t f`
is `f ()`, `noteInstance d ok` is `ok`, `note j a` is `a`. The checker and
every theorem read those definitions, so tracing cannot change what is
accepted. The compiled hooks (`implemented_by`) run the same computation and,
when a trace file is open, record what it did: one JSON line per subtyping
question the checker asks, with the `Var` steps and the variance components
computed while answering it, and one line per event outside a question.
The recording is on the reporting side only: it reads results, never
supplies one. -/
namespace Verification.SubtypingTrace
open Lean

/-- The counts of one question in progress. -/
structure Frame where
  kind : String
  source : Nat
  target : Nat
  fuel : Nat
  instances : Nat := 0
  varSteps : Nat := 0
  depth : Nat := 0
  events : Array Json := #[]

initialize traceHandle : IO.Ref (Option IO.FS.Handle) ← IO.mkRef none
initialize traceFrames : IO.Ref (List Frame) ← IO.mkRef []

/-- Open the trace file: every later question is recorded in it. -/
def open_ (path : System.FilePath) : IO Unit := do
  let h ← IO.FS.Handle.mk path .write
  traceHandle.set (some h)

private def emit (j : Json) : BaseIO Unit := do
  if let some h ← traceHandle.get then
    let _ ← (do h.putStrLn j.compress; h.flush : IO Unit).toBaseIO

private unsafe def questionImpl (kind : String) (source target fuel : Nat) (f : Unit → Bool) : Bool :=
  match unsafeBaseIO traceHandle.get with
  | none => f ()
  | some _ => unsafeBaseIO do
      traceFrames.modify fun fs => { kind, source, target, fuel } :: fs
      let r ← (IO.lazyPure f).catchExceptions fun _ => pure (f ())
      match ← traceFrames.get with
      | fr :: rest =>
        traceFrames.set rest
        emit (Json.mkObj [("question", toJson fr.kind), ("source", toJson fr.source),
          ("target", toJson fr.target), ("holds", toJson r),
          ("instances", toJson fr.instances), ("varSteps", toJson fr.varSteps),
          ("varDepth", toJson fr.depth), ("events", Json.arr fr.events)])
      | [] => pure ()
      pure r

/-- A subtyping question of kind `kind` between types of sizes `source`
and `target`, answered by `f`, with `fuel` the depth its instances may nest. -/
@[implemented_by questionImpl]
def question (_kind : String) (_source _target _fuel : Nat) (f : Unit → Bool) : Bool := f ()

private unsafe def noteInstanceImpl (fuel : Nat) (ok : Bool) : Bool :=
  unsafeBaseIO do
    traceFrames.modify fun fs => match fs with
      | fr :: rest =>
        let d := fr.fuel - fuel
        { fr with instances := fr.instances + 1,
                  varSteps := fr.varSteps + (if ok then 1 else 0),
                  depth := if ok then max fr.depth d else fr.depth } :: rest
      | [] => []
    pure ok

/-- An `Inst` step tried with `fuel` levels left, and whether it held. -/
@[implemented_by noteInstanceImpl]
def noteInstance (_fuel : Nat) (ok : Bool) : Bool := ok

private unsafe def noteImpl {α : Type} (j : Unit → Json) (a : α) : α :=
  match unsafeBaseIO traceHandle.get with
  | none => a
  | some _ => unsafeBaseIO do
    let fs ← traceFrames.get
    match fs with
    | fr :: rest => traceFrames.set ({ fr with events := fr.events.push (j ()) } :: rest)
    | [] => emit (j ())
    pure a

/-- An event of the computation producing `a`: recorded in the question in
progress, or on its own line. -/
@[implemented_by noteImpl]
def note {α : Type} (_j : Unit → Json) (a : α) : α := a

end Verification.SubtypingTrace
