import Verification.Calculus.Programs
import Verification.Calculus.TypeOperations

/-!
One well-typed program, shared by the three tests that have to agree about it.

`Tests/Typing.lean` derives it from the rules, `Tests/Checker.lean` has the
decision procedure accept it, and `Tests/Programs.lean` runs it. Those three
checks say something together only because they are about the same program;
three separate programs would give three unrelated facts. That is the only
reason this file exists, and the only kind of thing that belongs in it.

A test that needs a program of a particular shape -- one that gets stuck, one
that exercises a single expression form, one the checker must reject -- should
build it locally instead. Sharing it here would couple files that have no
reason to agree.

    function f(x: string | number): string {
      if (typeof x === "string") { return x }
      return "n"
    }
-/

namespace Verification
namespace Tests

open Core

-- The TypeScript type `string | number`.
def exStrOrNum : Ty := ofAtoms [.str, .num]

def exCond : Core.Exp := .eq (.tyof (.var "x")) (.lit (.vstr "string"))

def exFn : Core.Fn :=
  { name := "f"
    params := [("x", exStrOrNum)]
    ret := ofAtom .str
    body := [ .ite exCond [.ret (.var "x")] [], .ret (.lit (.vstr "n")) ] }

def exProg : Core.Prog := [exFn]

end Tests
end Verification
