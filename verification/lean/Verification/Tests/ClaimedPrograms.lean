import Verification.Lowering
import Verification.SkjsTypeClaims

/-!
Source programs paired with the claims SKJS would emit for them.

Three tests have to agree about each: `Tests/Lowering.lean` lowers it,
`Tests/Verify.lean` checks it, and `Tests/Programs.lean` runs the result.
They mean something together only because they are about the same program.

Spans are chosen rather than parsed -- these fixtures exercise the Lean side,
not the front end -- but they are internally consistent: an expression's claim
is keyed by its own span, and a statement's environment by its start.
-/

namespace Verification
namespace Tests

open Core

def str_ : Ty := ofAtom .str
def num_ : Ty := ofAtom .num
def strOrNum : Ty := ofAtoms [.str, .num]
def boolT : Ty := ofAtom .bool

/-! ## `narrowing`: both arms return, so the graph has no join.

    function f(x: string | number): string {
      if (typeof x === "string") { return x }
      return "n"
    }
-/

def narrowingCond : Expr :=
  .bin (12, 13) .eq (.tyof (14, 15) (.var (16, 17) "x")) (.lit (18, 19) (.vstr "string"))

def narrowingFn : Fn :=
  { name := "f", namePos := (0, 1)
    params := [{ name := "x", ty := strOrNum }]
    ret := str_
    body :=
      [ .ite (10, 11) narrowingCond [ .ret (20, 21) (.var (22, 23) "x") ] none
      , .ret (30, 31) (.lit (32, 33) (.vstr "n")) ] }

def narrowingClaims : FunTypeClaims :=
  { name := "f", namePos := (0, 1)
    params := [("x", some strOrNum)]
    ret := some str_
    envs := [ (10, [("x", some strOrNum)])
            , (20, [("x", some str_)])
            , (30, [("x", some num_)]) ]
    exprs := [ ((16, 17), some strOrNum), ((14, 15), some str_)
             , ((18, 19), some (ofAtom (.strLit "string"))), ((12, 13), some boolT)
             , ((22, 23), some str_), ((32, 33), some (ofAtom (.strLit "n"))) ] }

/-! ## `merging`: the `then` arm falls through, so its exit and the false edge
meet at the `return`. That node has two predecessors -- the case the block
representation could not express.

    function g(b: boolean): string {
      if (b) { const y = "a"; }
      return "z";
    }
-/

def mergingFn : Fn :=
  { name := "g", namePos := (0, 1)
    params := [{ name := "b", ty := boolT }]
    ret := str_
    body :=
      [ .ite (10, 11) (.var (12, 13) "b")
          [ .cst (20, 21) "y" none (.lit (22, 23) (.vstr "a")) ] none
      , .ret (30, 31) (.lit (32, 33) (.vstr "z")) ] }

def mergingClaims : FunTypeClaims :=
  { name := "g", namePos := (0, 1)
    params := [("b", some boolT)]
    ret := some str_
    -- `y` is not in scope at offset 30: it was declared inside the branch.
    envs := [ (10, [("b", some boolT)])
            , (20, [("b", some boolT)])
            , (30, [("b", some boolT)]) ]
    exprs := [ ((12, 13), some boolT), ((22, 23), some (ofAtom (.strLit "a")))
             , ((32, 33), some (ofAtom (.strLit "z"))) ] }

/-! ## `shadowing`: an inner `const` shadows an outer one and the branch falls
through. The continuation must read the *outer* binding. Both have type
`string`, so no edge check would catch a mix-up -- only slot resolution does.

    function h(b: boolean): string {
      const x = "outer";
      if (b) { const x = "inner"; }
      return x;
    }
-/

def shadowingFn : Fn :=
  { name := "h", namePos := (0, 1)
    params := [{ name := "b", ty := boolT }]
    ret := str_
    body :=
      [ .cst (10, 11) "x" none (.lit (12, 13) (.vstr "outer"))
      , .ite (20, 21) (.var (22, 23) "b")
          [ .cst (40, 41) "x" none (.lit (42, 43) (.vstr "inner")) ] none
      , .ret (30, 31) (.var (32, 33) "x") ] }

def shadowingClaims : FunTypeClaims :=
  { name := "h", namePos := (0, 1)
    params := [("b", some boolT)]
    ret := some str_
    envs := [ (10, [("b", some boolT)])
            , (20, [("b", some boolT), ("x", some (ofAtom (.strLit "outer")))])
            , (40, [("b", some boolT), ("x", some (ofAtom (.strLit "outer")))])
            , (30, [("b", some boolT), ("x", some (ofAtom (.strLit "outer")))]) ]
    exprs := [ ((12, 13), some (ofAtom (.strLit "outer"))), ((22, 23), some boolT)
             , ((42, 43), some (ofAtom (.strLit "inner")))
             , ((32, 33), some (ofAtom (.strLit "outer"))) ] }

/-! ## `nested`: an `if` inside a falling-through `if`, and both arms of the
inner one fall through. The inner merge is itself a predecessor of the outer
merge, so the `return` is reached along three paths.

    function k(b: boolean, c: boolean): string {
      if (b) {
        if (c) { const p = "p"; } else { const q = "q"; }
      }
      return "z";
    }
-/

def nestedFn : Fn :=
  { name := "k", namePos := (0, 1)
    params := [{ name := "b", ty := boolT }, { name := "c", ty := boolT }]
    ret := str_
    body :=
      [ .ite (10, 11) (.var (12, 13) "b")
          [ .ite (20, 21) (.var (22, 23) "c")
              [ .cst (40, 41) "p" none (.lit (42, 43) (.vstr "p")) ]
              (some [ .cst (50, 51) "q" none (.lit (52, 53) (.vstr "q")) ]) ]
          none
      , .ret (30, 31) (.lit (32, 33) (.vstr "z")) ] }

private def bc : List (String × Option Ty) := [("b", some boolT), ("c", some boolT)]

def nestedClaims : FunTypeClaims :=
  { name := "k", namePos := (0, 1)
    params := [("b", some boolT), ("c", some boolT)]
    ret := some str_
    -- Neither `p` nor `q` is in scope at offset 30: both were declared inside
    -- the inner branch, and the outer merge forgets them.
    envs := [ (10, bc), (20, bc), (40, bc), (50, bc), (30, bc) ]
    exprs := [ ((12, 13), some boolT), ((22, 23), some boolT)
             , ((42, 43), some (ofAtom (.strLit "p")))
             , ((52, 53), some (ofAtom (.strLit "q")))
             , ((32, 33), some (ofAtom (.strLit "z"))) ] }

/-! ## `bothFall`: an `if`/`else` where *neither* arm returns. Two edges meet
at the continuation with no branch-free path between them.

    function m(b: boolean): string {
      if (b) { const y = "a"; } else { const y = "b"; }
      return "z";
    }
-/

def bothFallFn : Fn :=
  { name := "m", namePos := (0, 1)
    params := [{ name := "b", ty := boolT }]
    ret := str_
    body :=
      [ .ite (10, 11) (.var (12, 13) "b")
          [ .cst (20, 21) "y" none (.lit (22, 23) (.vstr "a")) ]
          (some [ .cst (40, 41) "y" none (.lit (42, 43) (.vstr "b")) ])
      , .ret (30, 31) (.lit (32, 33) (.vstr "z")) ] }

def bothFallClaims : FunTypeClaims :=
  { name := "m", namePos := (0, 1)
    params := [("b", some boolT)]
    ret := some str_
    envs := [ (10, [("b", some boolT)]), (20, [("b", some boolT)])
            , (40, [("b", some boolT)]), (30, [("b", some boolT)]) ]
    exprs := [ ((12, 13), some boolT), ((22, 23), some (ofAtom (.strLit "a")))
             , ((42, 43), some (ofAtom (.strLit "b")))
             , ((32, 33), some (ofAtom (.strLit "z"))) ] }

/-! ## `annotated`: a `const` with a source annotation.

The core has no place for the annotation -- `Node.set` binds whatever the
initialiser has -- so it travels in `NodeInfo` and is checked by the verifier.
It is a requirement the source makes, not something the calculus needs.

    function n(): string {
      const s: string = "a";
      return s;
    }
-/

def annotatedFn : Fn :=
  { name := "n", namePos := (0, 1)
    params := []
    ret := str_
    body :=
      [ .cst (10, 11) "s" (some str_) (.lit (12, 13) (.vstr "a"))
      , .ret (20, 21) (.var (22, 23) "s") ] }

def annotatedClaims : FunTypeClaims :=
  { name := "n", namePos := (0, 1)
    params := []
    ret := some str_
    envs := [ (10, []), (20, [("s", some str_)]) ]
    exprs := [ ((12, 13), some (ofAtom (.strLit "a"))), ((22, 23), some str_) ] }

/-- The same shape with a number where the annotation says `string`. -/
def badAnnotatedFn : Fn :=
  { annotatedFn with
      body :=
        [ .cst (10, 11) "s" (some str_) (.lit (12, 13) (.vnum 5))
        , .ret (20, 21) (.var (22, 23) "s") ] }

def badAnnotatedClaims : FunTypeClaims :=
  { annotatedClaims with
      exprs := [ ((12, 13), some (ofAtom (.numLit 5))), ((22, 23), some str_) ] }

/-! ## `tdz`: a read of a binding declared later in the same block.

A declaration binds throughout its block, so the `return` refers to the inner
`x`, which has no value yet. JavaScript throws `ReferenceError` and TypeScript
rejects the program; the verifier must reject it too, and must not quietly
read the outer binding instead. The claims here describe the outer `x`, which
is what SKJS's declaration-point scoping records -- so the rejection cannot
come from the claims and has to come from resolution.

    function t(b: boolean): string {
      const x = "outer";
      if (b) {
        return x;              // the inner x, not yet initialized
        const x = "inner";
      }
      return x;
    }
-/

def outerT : Ty := ofAtom (.strLit "outer")
def innerT : Ty := ofAtom (.strLit "inner")

def tdzFn : Fn :=
  { name := "t", namePos := (0, 1)
    params := [{ name := "b", ty := boolT }]
    ret := str_
    body :=
      [ .cst (10, 11) "x" none (.lit (12, 13) (.vstr "outer"))
      , .ite (20, 21) (.var (22, 23) "b")
          [ .ret (60, 61) (.var (62, 63) "x")
          , .cst (40, 41) "x" none (.lit (42, 43) (.vstr "inner")) ] none
      , .ret (30, 31) (.var (32, 33) "x") ] }

def tdzClaims : FunTypeClaims :=
  { name := "t", namePos := (0, 1)
    params := [("b", some boolT)]
    ret := some str_
    envs := [ (10, [("b", some boolT)])
            , (20, [("b", some boolT), ("x", some outerT)])
            , (60, [("b", some boolT), ("x", some outerT)])
            , (40, [("b", some boolT), ("x", some outerT)])
            , (30, [("b", some boolT), ("x", some outerT)]) ]
    exprs := [ ((12, 13), some outerT), ((22, 23), some boolT), ((62, 63), some outerT)
             , ((42, 43), some innerT), ((32, 33), some outerT) ] }

/-! ## `hiddenOuter`: a shadowed binding still needed after the block.

Inside the branch the name `x` means the inner binding, so no claim there
names the outer one -- but the `return` after the block still needs it. Its
type is carried from the claim at the declaration that shadowed it.

    function h(b: boolean): string {
      const x = "outer";
      if (b) {
        const x = "inner";
        const y = x;
      }
      return x;
    }
-/

def hiddenOuterFn : Fn :=
  { name := "h", namePos := (0, 1)
    params := [{ name := "b", ty := boolT }]
    ret := str_
    body :=
      [ .cst (10, 11) "x" none (.lit (12, 13) (.vstr "outer"))
      , .ite (20, 21) (.var (22, 23) "b")
          [ .cst (40, 41) "x" none (.lit (42, 43) (.vstr "inner"))
          , .cst (50, 51) "y" none (.var (52, 53) "x") ] none
      , .ret (30, 31) (.var (32, 33) "x") ] }

def hiddenOuterClaims : FunTypeClaims :=
  { name := "h", namePos := (0, 1)
    params := [("b", some boolT)]
    ret := some str_
    envs := [ (10, [("b", some boolT)])
            , (20, [("b", some boolT), ("x", some outerT)])
            , (40, [("b", some boolT), ("x", some outerT)])
            , (50, [("b", some boolT), ("x", some innerT)])
            , (30, [("b", some boolT), ("x", some outerT)]) ]
    exprs := [ ((12, 13), some outerT), ((22, 23), some boolT)
             , ((42, 43), some innerT), ((52, 53), some innerT)
             , ((32, 33), some outerT) ] }

/-! ## `dead`: a statement after a `return`.

It cannot run, so it is not lowered and carries none of the obligations of
reachable code -- in particular it is not required to have anywhere to
continue to. SKJS checks such statements and emits claims for them; those
claims are simply not consumed.

    function d(): string {
      return "ok";
      const y = "dead";
    }
-/

def deadFn : Fn :=
  { name := "d", namePos := (0, 1)
    params := []
    ret := str_
    body :=
      [ .ret (10, 11) (.lit (12, 13) (.vstr "ok"))
      , .cst (20, 21) "y" none (.lit (22, 23) (.vstr "dead")) ] }

def deadClaims : FunTypeClaims :=
  { name := "d", namePos := (0, 1)
    params := []
    ret := some str_
    envs := [ (10, []), (20, []) ]
    exprs := [ ((12, 13), some (ofAtom (.strLit "ok")))
             , ((22, 23), some (ofAtom (.strLit "dead"))) ] }

end Tests
end Verification
