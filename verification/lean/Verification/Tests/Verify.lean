import Verification.Verify
import Verification.Tests.ClaimedPrograms

/-!
Pins `Verify.lean`: whole functions accepted and rejected.

Not in the trusted base -- a bug here causes a rejection, not an unsound
acceptance. What belongs here is that the checker accepts what it should and
rejects what it should, since `checkFile_sound` is satisfied by a checker that
rejects everything.

The merge cases are the point of the graph representation: a branch that falls
through reaches the continuation from two predecessors, and each must justify
the environment claimed there.
-/

namespace Verification
namespace Tests

open Core

/-! ### Accepted -/

-- Both arms return: no join, the case the block representation also handled.
#guard checkFile [narrowingFn] [narrowingClaims] matches .ok _

-- The `then` arm falls through: a real join at the `return`.
#guard checkFile [mergingFn] [mergingClaims] matches .ok _

-- An inner `const` shadows an outer one across a falling-through branch.
#guard checkFile [shadowingFn] [shadowingClaims] matches .ok _

-- Both arms fall through: two predecessors and no straight-line path.
#guard checkFile [bothFallFn] [bothFallClaims] matches .ok _

-- Nested merges: the inner join is itself a predecessor of the outer one, so
-- the `return` has to be justified along three paths.
#guard checkFile [nestedFn] [nestedClaims] matches .ok _

-- A `const` whose initialiser fits its annotation.
#guard checkFile [annotatedFn] [annotatedClaims] matches .ok _

/-! ### Rejected: a `const` initialiser outside its annotation

The annotation is a requirement the source makes. The calculus does not need
it -- `NodeOk.set` binds whatever the initialiser has -- so this obligation
lives in the verifier, and would be silently lost if the annotation were
dropped during lowering. -/

#guard (checkFile [badAnnotatedFn] [badAnnotatedClaims] matches .error _)

-- A shadowed binding needed again after the block: its type is carried from
-- the declaration that shadowed it, which no claim inside the block names.
#guard checkFile [hiddenOuterFn] [hiddenOuterClaims] matches .ok _

-- Dead code cannot run, so it carries none of the obligations of reachable
-- code -- in particular it need not have anywhere to continue to.
#guard checkFile [deadFn] [deadClaims] matches .ok _

/-! ### Rejected: reading a binding declared later in the same block

A declaration binds throughout its block, so the `return` refers to the inner
`x`, which nothing has set on that path. JavaScript throws `ReferenceError`
here and TypeScript rejects the program. The claims describe the *outer* `x`,
as SKJS's declaration-point scoping records, so this rejection comes from
resolution rather than from anything the claims say. -/

#guard (checkFile [tdzFn] [tdzClaims] matches .error _)

/-! ### Rejected: the claim at a merge must be justified by *both* edges

Narrowing the merge to what only the true edge establishes. The false edge
cannot cover it, which is exactly the check a block representation had no
place to make. -/

private def badMergeClaims : FunTypeClaims :=
  { mergingClaims with
      envs := [ (10, [("b", some boolT)])
              , (20, [("b", some boolT)])
              , (30, [("b", some boolT), ("y", some (ofAtom (.strLit "a")))]) ] }

#guard (checkFile [mergingFn] [badMergeClaims] matches .error _)

/-! ### Rejected: a nested merge justified by only one of its three paths

Claiming `p` at the outer merge. The arm that binds `p` could justify it; the
other arm and the outer false edge cannot. -/

private def badNestedClaims : FunTypeClaims :=
  { nestedClaims with
      envs := [ (10, [("b", some boolT), ("c", some boolT)])
              , (20, [("b", some boolT), ("c", some boolT)])
              , (40, [("b", some boolT), ("c", some boolT)])
              , (50, [("b", some boolT), ("c", some boolT)])
              , (30, [("b", some boolT), ("c", some boolT),
                      ("p", some (ofAtom (.strLit "p")))]) ] }

#guard (checkFile [nestedFn] [badNestedClaims] matches .error _)

/-! ### Rejected: a claim narrower than the values that reach it -/

private def neverClaims : FunTypeClaims :=
  { narrowingClaims with
      exprs := [ ((16, 17), some strOrNum), ((14, 15), some str_)
               , ((18, 19), some (ofAtom (.strLit "string"))), ((12, 13), some boolT)
               , ((22, 23), some never), ((32, 33), some (ofAtom (.strLit "n"))) ] }

#guard (checkFile [narrowingFn] [neverClaims] matches .error _)

/-! ### Rejected: control falling out of the function

Dropping the trailing `return` leaves the false edge of the `if` with nowhere
to go. `Edge` cannot justify leaving the graph, so this is rejected -- the
"a function may not fall off the end" requirement, which survives the removal
of "every branch must return". -/

private def fallsOffFn : Fn :=
  { mergingFn with
      body := [ .ite (10, 11) (.var (12, 13) "b")
                  [ .cst (20, 21) "y" none (.lit (22, 23) (.vstr "a")) ] none ] }

#guard (checkFile [fallsOffFn] [mergingClaims] matches .error _)

/-! ### Rejected: a missing claim

Every node's entry environment comes from the claim at the statement it was
lowered from, so a statement with no recorded environment is a rejection
rather than something the checker silently derives. -/

private def missingEnvClaims : FunTypeClaims :=
  { mergingClaims with envs := [ (10, [("b", some boolT)]), (20, [("b", some boolT)]) ] }

#guard (checkFile [mergingFn] [missingEnvClaims] matches .error _)

/-! ### Rejected: the claims are not bound to this declaration -/

#guard (checkFile [mergingFn] [narrowingClaims] matches .error _)

end Tests
end Verification
