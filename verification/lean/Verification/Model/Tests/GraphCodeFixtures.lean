import Verification.Model.Source.RequestJson

/-! Graph code for hand-written test programs. A closure whose code is one
expression is graph code of one node, `return e`, run from the frame its
signature describes: the receiver, the parameters, then every slot of the
context the closure is created in, which it captures in order: in the node,
slot 0 is the receiver, the parameters follow, then the captures. -/
namespace Verification.Model.GraphCodeFixtures
open ProgramTyping RequestJson Lean

/-- One-node code of `arity` returning `body`, capturing the `context` slots of
the context it is created in. -/
def oneNode (arity : Nat) (body : Tm) (context : Nat) (kind : Invoke := .call) : CallCode :=
  .graph arity [body] [(.ret, none)] 0 ((List.range context).map .var) kind

/-- Its code requests at the signatures `sigs`, created in the context `Γ`:
one per signature, its one node claimed at the signature's frame and result. -/
def oneNodeCodes (arity : Nat) (body : Tm) (Γ : List (Ty Nat))
    (sigs : List (Ty Nat × List (Ty Nat) × Ty Nat)) : List CodeRequest :=
  sigs.map fun s => ⟨⟨arity, [body], [(.ret, none)], 0, Γ, s, none⟩, [⟨s.1 :: s.2.1.take arity ++ Γ, s.2.2⟩]⟩

/-- Every code admitted: whether a code meets its signatures is its table's
question, not its creation's. -/
def admitted : CodeEntry Nat → Bool := fun _ => true

/-- Produce evidence for a request, then check it through the JSON consumer. -/
def roundtrip (r : Request) (fuel : Nat := 10) : Except String Unit := do
  let r ← Json.parse (toJson r).compress
  let c ← produceJson r fuel
  verifyJson r (← Json.parse c.compress)

def ok (x : Except String α) : Bool := match x with | .ok _ => true | .error _ => false
end Verification.Model.GraphCodeFixtures

/-- One step of the machine on a test program's ground term: the step rules a
hand-written program takes, a run of graph code's included, inside the
evaluation contexts it takes them in. -/
syntax "machine_step" : tactic
macro_rules
  | `(tactic| machine_step) => `(tactic| first
    | exact .makeV rfl
    | exact .readV rfl
    | exact .writeV rfl (by decide)
    | exact .letV rfl
    | exact .iteT
    | exact .iteF
    | exact .testV rfl
    | exact .callGraph rfl (by decide)
    | exact .constructGraph (by decide)
    | exact .callBound rfl (by decide)
    | exact .gotoEnter rfl rfl
    | exact .frameRet rfl
    | exact .frameEffect rfl
    | exact .frameBind rfl
    | (apply Verification.Model.Step.frameC; machine_step)
    | (apply Verification.Model.Step.letC; machine_step)
    | (apply Verification.Model.Step.iteC; machine_step)
    | (apply Verification.Model.Step.makeC; machine_step)
    | (apply Verification.Model.Step.appR rfl; machine_step)
    | (apply Verification.Model.Step.callL; machine_step))

/-- Run a hand-written program by the machine to its end. -/
macro "run_machine" : tactic => `(tactic| repeat first
  | exact Verification.Model.ControlFlow.Execution.refl
  | apply Verification.Model.ControlFlow.Execution.next (.enter rfl)
  | apply Verification.Model.ControlFlow.Execution.next (.bind rfl)
  | apply Verification.Model.ControlFlow.Execution.next (.effect rfl)
  | apply Verification.Model.ControlFlow.Execution.next (.ret rfl)
  | apply Verification.Model.ControlFlow.Execution.next .yesBind
  | apply Verification.Model.ControlFlow.Execution.next .noBind
  | apply Verification.Model.ControlFlow.Execution.next .yes
  | apply Verification.Model.ControlFlow.Execution.next .no
  | apply Verification.Model.ControlFlow.Execution.next (.expr (by machine_step)))
