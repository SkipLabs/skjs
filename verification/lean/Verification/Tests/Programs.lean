import Verification.Calculus.Programs
import Verification.Tests.ClaimedPrograms

/-!
Pins `Calculus/Programs.lean`: the observations, the value environments, and
the fuel-indexed graph evaluator.

**These definitions are in the trusted base, and nothing else in the project
runs them.** The verifier executes `checkFile`, never `run`; the program
corpus exercises the verifier. `run` appears in `Verify.lean` only inside
theorem statements. So these checks are the only evidence that the semantics
computes anything at all.

Soundness does not constrain it either: `sound` concludes `run … ≠ .stuck` and
`run … = .ok v → mem v f.ret`, both of which hold for a `run` that always
returns `.timeout`. That is what makes this file load-bearing.

What belongs here: one case per node form, both outcomes of each `.stuck`
guard, and the fuel boundary. Build whatever graph a case needs -- one that
gets stuck is as welcome as one that returns.

Not yet covered: `.not`, `.ne`, `.and`, `.or`, `.call`, and so `evalArgs` and
`lookupFun`.
-/

namespace Verification
namespace Tests

open Core

/-! ### Fuel -/

#guard evalE [] 0 [] (.lit (.vbool true)) matches .timeout
#guard run [] 0 { name := "f", params := [], ret := unknown, code := [] } 0 [] matches .timeout

/-! ### Going wrong -/

private def emptyFn : Core.Fn := { name := "f", params := [], ret := unknown, code := [] }

-- An unbound variable.
#guard evalE [] 5 [] (.var "x") matches .stuck

-- A label with no node: control may not fall out of a function.
#guard run [] 5 emptyFn 0 [] matches .stuck

-- A successor that leaves the graph, which is what lowering emits when a
-- path reaches the end of a body without returning.
#guard run [] 5 { emptyFn with code := [.set "x" (.lit (.vbool true)) none] } 0 []
        matches .stuck

-- A non-boolean condition.
#guard run [] 5 { emptyFn with code := [.branch (.lit (.vstr "x")) (some 0) (some 0)] } 0 []
        matches .stuck

/-! ### Observations -/

#guard typeofVal .vnull == "object"
#guard typeofVal .vundef == "undefined"
#guard typeofVal (.vbool true) == "boolean"

/-! ### Environments

A binding prepends and lookup takes the first match. -/

#guard venvGet (venvSet [("x", .vbool true)] "x" (.vbool false)) "x"
        == some (Val.vbool false)

-- Fewer values than parameters binds nothing; `evalE`'s `.call` guards arity
-- before it gets here. (The parameter type is `unknown`.)
#guard bindParams [("x", unknown)] [] == []

/-! ### Running the lowered example programs

Both paths of `narrowingFn` return, and both land in the declared return type
(`accepted_returns_in_type` says the second part in general). -/

private def narrowingGraph : Core.Fn := (lowerFn narrowingFn).fn
private def narrowingProg : Core.Prog := lowerProg [narrowingFn]

#guard run narrowingProg 20 narrowingGraph 0 (bindParams narrowingGraph.params [.vstr "hi"])
        matches .ok (.vstr "hi")

#guard run narrowingProg 20 narrowingGraph 0 (bindParams narrowingGraph.params [.vnum 7])
        matches .ok (.vstr "n")

/-! ### The merge really is reached from both sides -/

private def mergingGraph : Core.Fn := (lowerFn mergingFn).fn
private def mergingProg : Core.Prog := lowerProg [mergingFn]

#guard run mergingProg 20 mergingGraph 0 (bindParams mergingGraph.params [.vbool true])
        matches .ok (.vstr "z")

#guard run mergingProg 20 mergingGraph 0 (bindParams mergingGraph.params [.vbool false])
        matches .ok (.vstr "z")

/-! ### Shadowing: the continuation reads the outer binding

If lowering leaked the branch's `x`, the true path would return `"inner"`. -/

private def shadowingGraph : Core.Fn := (lowerFn shadowingFn).fn
private def shadowingProg : Core.Prog := lowerProg [shadowingFn]

#guard run shadowingProg 20 shadowingGraph 0 (bindParams shadowingGraph.params [.vbool true])
        matches .ok (.vstr "outer")

#guard run shadowingProg 20 shadowingGraph 0 (bindParams shadowingGraph.params [.vbool false])
        matches .ok (.vstr "outer")

/-! ### Every path through a nested merge returns

Node 4 is reached three ways; all of them arrive at the same `return`. -/

private def nestedGraph : Core.Fn := (lowerFn nestedFn).fn
private def nestedProg : Core.Prog := lowerProg [nestedFn]

#guard run nestedProg 30 nestedGraph 0
        (bindParams nestedGraph.params [.vbool true, .vbool true]) matches .ok (.vstr "z")
#guard run nestedProg 30 nestedGraph 0
        (bindParams nestedGraph.params [.vbool true, .vbool false]) matches .ok (.vstr "z")
#guard run nestedProg 30 nestedGraph 0
        (bindParams nestedGraph.params [.vbool false, .vbool true]) matches .ok (.vstr "z")

end Tests
end Verification
