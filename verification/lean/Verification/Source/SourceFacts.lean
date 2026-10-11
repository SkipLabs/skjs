import Verification.Source.Fragment

namespace Verification.SourceExtraction
open Fragment

mutual
/-- Storage is selected from source assignments, including writes in nested
closures. Active-name shadowing is rejected by the lowering, so a matching
name cannot silently designate a different binding. Producer claims cannot
choose which parameters are mutable. -/
private partial def assignsExpr (name : String) : Fragment.Expr → Bool
  | .var .. | .lit .. => false
  | .assign _ target _ rhs | .nullishAssign _ target _ rhs => target == name || assignsExpr name rhs
  | .lambda _ _ _ _ defaults _ _ e =>
    defaults.attach.any (fun ⟨d,_⟩ => assignsExpr name d.2) || assignsExpr name e
  | .not _ e | .unary _ _ e | .cast _ _ e | .read _ _ e | .shapeTest _ _ _ e =>
    assignsExpr name e
  | .equality _ _ a b | .logical _ _ a b | .coalesce _ a b | .optional _ _ a b
  | .singletonTest _ _ _ _ a b | .write _ _ a b | .withValue _ a b _ _ | .index _ _ a b =>
    assignsExpr name a || assignsExpr name b
  | .indexWrite _ _ a b c | .elemWrite _ a b c => assignsExpr name a || assignsExpr name b || assignsExpr name c
  | .arith _ _ a b | .elemAt _ a b | .comma _ a b | .inKeys _ a b => assignsExpr name a || assignsExpr name b
  | .arrayLit _ es => es.any (assignsExpr name)
  | .arrayAssign _ targets rest rhs => targets.any (fun q => q.name == name ||
      (q.default_.map (assignsExpr name)).getD false) || rest.any (·.2.2.name == name) ||
      assignsExpr name rhs
  | .logicalAssign _ _ target rhs =>
    (match target with | .var _ n => n == name | _ => false) ||
      assignsExpr name target || assignsExpr name rhs
  | .update _ _ target rhs _ =>
    (match target with | .var _ n => n == name | _ => false) ||
      assignsExpr name target || (rhs.map (assignsExpr name)).getD false
  | .alloc _ _ es | .build _ _ es => es.any (assignsExpr name)
  | .call _ f args _ _ | .invoke _ f args _ _ => assignsExpr name f || args.any (assignsExpr name)
  | .callWithReceiver _ f r args | .bindWithReceiver _ f r args =>
    assignsExpr name f || assignsExpr name r || args.any (assignsExpr name)
  | .ctor _ lam => assignsExpr name lam
  | .objectAssign _ t ss => assignsExpr name t || ss.any (assignsExpr name)
  | .construct _ f args _ _ => assignsExpr name f || args.any (assignsExpr name)
  | .applyWithReceiver _ f r list =>
    assignsExpr name f || assignsExpr name r || (list.map (assignsExpr name)).getD false
  | .ifBody _ c t e => assignsExpr name c || assignsExpr name t || assignsExpr name e
  | .block _ ss => ss.any (assignsStmt name)

partial def assignsStmt (name : String) : Fragment.Stmt → Bool
  | .ret _ e | .effect _ e | .throw _ e => assignsExpr name e
  | .tryStmt _ b h f => b.any (assignsStmt name) || ((h.map (·.2)).getD []).any (assignsStmt name) ||
    (f.getD []).any (assignsStmt name)
  | .constants _ bs | .mutables _ bs => bs.any fun b => assignsExpr name b.init
  | .destructure _ target d init => assignsExpr name init ||
    (d.toList ++ target.defaults).any (assignsExpr name)
  | .ite _ c t e => assignsExpr name c || t.any (assignsStmt name) ||
    (e.getD []).any (assignsStmt name)
  | .loop _ c b u => assignsExpr name c || b.any (assignsStmt name) || u.any (assignsStmt name)
  | .forOf _ _ _ _ i b => assignsExpr name i || b.any (assignsStmt name)
  | .block _ _ b => b.any (assignsStmt name)
  | .closing _ c b => c.any (assignsStmt name) || b.any (assignsStmt name)
  | .brk .. | .cont .. => false
end

/-- Every name a statement's expressions mention, bound or not: a superset of
the module functions its body can reach. -/
partial def stmtNames : Fragment.Stmt → List String
  | .ret _ e | .effect _ e | .throw _ e => e.freeNames
  | .tryStmt _ b h f => b.flatMap stmtNames ++ ((h.map (·.2)).getD []).flatMap stmtNames ++
    (f.getD []).flatMap stmtNames
  | .constants _ bs | .mutables _ bs => bs.flatMap fun b => b.init.freeNames
  | .destructure _ target d init => init.freeNames ++
    (d.toList ++ target.defaults).flatMap Fragment.Expr.freeNames ++ target.slices.map (Fragment.restFromName ·.2)
  | .ite _ c t e => c.freeNames ++ t.flatMap stmtNames ++ (e.getD []).flatMap stmtNames
  | .loop _ c b u => c.freeNames ++ b.flatMap stmtNames ++ u.flatMap stmtNames
  | .forOf _ _ _ it i b => it :: i.freeNames ++ b.flatMap stmtNames
  | .block _ _ b => b.flatMap stmtNames
  | .closing _ c b => c.flatMap stmtNames ++ b.flatMap stmtNames
  | .brk .. | .cont .. => []

/-! ### Owned objects

A key-adding write is lowered as a copy (`Tm.merge`, allocation from parts)
of the object with the key added, rebound to the local that held it. That is
JavaScript's in-place write only where nothing else can observe the object
the copy replaces: the local's own fresh allocation, which no other reference
has reached. The analysis is syntactic and decides only which lowering a
write gets; the copy is checked by the merge rule like any other. -/

/-- Whether `n` may reach a place other than the receiver of a member read or
write of `n`: another binding, a field, an argument or `this` of a call, a
result, a capture. Reads, writes, index reads and `in` tests of `n`'s own
members only look at the object. Any other occurrence counts, and every
occurrence inside a closure does, since the closure holds the object. -/
partial def escapesExpr (n : String) : Fragment.Expr → Bool
  | .var _ m => m == n
  | .lit .. => false
  | .read _ _ (.var ..) => false
  | .index _ _ (.var ..) key => escapesExpr n key
  | .write _ _ (.var ..) rhs => escapesExpr n rhs
  | .indexWrite _ _ (.var ..) key rhs => escapesExpr n key || escapesExpr n rhs
  | .inKeys _ key (.var ..) => escapesExpr n key
  | .shapeTest _ (.hasKey _) _ (.var ..) => false
  | .update _ _ (.read _ _ (.var ..)) rhs _ => (rhs.map (escapesExpr n)).getD false
  | .update _ _ (.index _ _ (.var ..) key) rhs _ =>
    escapesExpr n key || (rhs.map (escapesExpr n)).getD false
  | .logicalAssign _ _ (.read _ _ (.var ..)) rhs => escapesExpr n rhs
  | .logicalAssign _ _ (.index _ _ (.var ..) key) rhs => escapesExpr n key || escapesExpr n rhs
  -- `Object.assign(o, …)` copies onto `o`, as a write does; its value is `o`,
  -- which only its statement form, whose value no one reads, lowers.
  | .objectAssign _ (.var ..) ss => ss.any (escapesExpr n)
  -- A method call passes its object as `this`.
  | .invoke _ (.read _ _ (.var _ m)) args _ _ => m == n || args.any (escapesExpr n)
  | .invoke _ (.index _ _ (.var _ m) key) args _ _ =>
    m == n || escapesExpr n key || args.any (escapesExpr n)
  | e@(.lambda ..) | e@(.ctor ..) | e@(.block ..) | e@(.ifBody ..) | e@(.optional ..)
  | e@(.withValue ..) | e@(.arrayAssign ..) | e@(.assign ..) | e@(.nullishAssign ..) =>
    e.freeNames.contains n
  | .not _ e | .unary _ _ e | .cast _ _ e | .read _ _ e | .shapeTest _ _ _ e => escapesExpr n e
  | .equality _ _ a b | .logical _ _ a b | .coalesce _ a b | .singletonTest _ _ _ _ a b
  | .write _ _ a b | .index _ _ a b | .arith _ _ a b | .elemAt _ a b | .comma _ a b
  | .inKeys _ a b | .logicalAssign _ _ a b => escapesExpr n a || escapesExpr n b
  | .indexWrite _ _ a b c | .elemWrite _ a b c => escapesExpr n a || escapesExpr n b || escapesExpr n c
  | .update _ _ a b _ => escapesExpr n a || (b.map (escapesExpr n)).getD false
  | .alloc _ _ es | .build _ _ es | .arrayLit _ es => es.any (escapesExpr n)
  | .call _ f args _ _ | .invoke _ f args _ _ | .construct _ f args _ _ =>
    escapesExpr n f || args.any (escapesExpr n)
  | .callWithReceiver _ f r args | .bindWithReceiver _ f r args =>
    escapesExpr n f || escapesExpr n r || args.any (escapesExpr n)
  | .applyWithReceiver _ f r list =>
    escapesExpr n f || escapesExpr n r || (list.map (escapesExpr n)).getD false
  | .objectAssign _ t ss => escapesExpr n t || ss.any (escapesExpr n)

/-- The closures' statement bodies an expression creates, where their own
owned objects are found. -/
partial def closureBodies : Fragment.Expr → List (List Fragment.Stmt)
  | .lambda _ _ _ _ ds _ _ b => ds.flatMap (fun d => closureBodies d.2) ++
    (match b with | .block _ ss => [ss] | b => closureBodies b)
  | .ctor _ lam => closureBodies lam
  | .var .. | .lit .. => []
  | .not _ e | .unary _ _ e | .cast _ _ e | .read _ _ e | .shapeTest _ _ _ e => closureBodies e
  | .equality _ _ a b | .logical _ _ a b | .coalesce _ a b | .singletonTest _ _ _ _ a b
  | .write _ _ a b | .index _ _ a b | .arith _ _ a b | .elemAt _ a b | .comma _ a b
  | .inKeys _ a b | .logicalAssign _ _ a b | .optional _ _ a b
  | .withValue _ a b _ _ => closureBodies a ++ closureBodies b
  | .indexWrite _ _ a b c | .elemWrite _ a b c | .ifBody _ a b c =>
    closureBodies a ++ closureBodies b ++ closureBodies c
  | .update _ _ a b _ => closureBodies a ++ (b.map closureBodies).getD []
  | .alloc _ _ es | .build _ _ es | .arrayLit _ es => es.flatMap closureBodies
  | .arrayAssign _ targets _ rhs => closureBodies rhs ++
    targets.flatMap fun q => (q.default_.map closureBodies).getD []
  | .assign _ _ _ e | .nullishAssign _ _ _ e => closureBodies e
  | .call _ f args _ _ | .invoke _ f args _ _ | .construct _ f args _ _ =>
    closureBodies f ++ args.flatMap closureBodies
  | .callWithReceiver _ f r args | .bindWithReceiver _ f r args =>
    closureBodies f ++ closureBodies r ++ args.flatMap closureBodies
  | .applyWithReceiver _ f r list =>
    closureBodies f ++ closureBodies r ++ (list.map closureBodies).getD []
  | .objectAssign _ t ss => closureBodies t ++ ss.flatMap closureBodies
  | .block _ ss => [ss]

/-- The analysis state: the owned locals in scope, each with the loop depth
of its declaration, and the key-adding writes found so far. -/
private structure Owned where
  locals : List (String × Nat) := []
  sites : List Span := []

mutual
/-- An expression runs: every owned local it may let escape stops being
owned, and the closures it creates are analysed as bodies of their own. -/
private partial def ownedExpr (e : Fragment.Expr) (s : Owned) : Owned :=
  let s := { s with locals := s.locals.filter fun (n, _) => !escapesExpr n e }
  (closureBodies e).foldl (fun s ss => { s with sites := (ownedStmts 0 ss {}).sites ++ s.sites }) s

/-- The statements in order at loop depth `d`. An `o.k = e` statement on an
owned `o` declared at the same depth is a key-adding site when `e` (and a
computed key) lets `o` escape nowhere: no other reference exists before the
write, and outside a loop the declaration does not enclose, the write runs
once per allocation. Later escapes are after the write in every run. -/
private partial def ownedStmts (d : Nat) : List Fragment.Stmt → Owned → Owned
  | [], s => s
  | st :: rest, s => ownedStmts d rest (ownedStmt d st s)

private partial def ownedStmt (d : Nat) (st : Fragment.Stmt) (s : Owned) : Owned :=
  match st with
  | .constants _ bs => bs.foldl (fun s b =>
      let s := ownedExpr b.init s
      let s := { s with locals := s.locals.filter (·.1 != b.name) }
      match b.init with
      | .alloc .. | .build .. => { s with locals := (b.name, d) :: s.locals }
      | _ => s) s
  | .mutables _ bs => bs.foldl (fun s b =>
      let s := ownedExpr b.init s
      { s with locals := s.locals.filter (·.1 != b.name) }) s
  | .effect _ e =>
    let site := match e with
      | .write _ _ (.var _ n) rhs =>
        if s.locals.contains (n, d) && !escapesExpr n rhs then some e.span else none
      | .indexWrite _ _ (.var _ n) key rhs =>
        if s.locals.contains (n, d) && !escapesExpr n key && !escapesExpr n rhs then some e.span
        else none
      | .objectAssign _ (.var _ n) ss =>
        if s.locals.contains (n, d) && !ss.any (escapesExpr n) then some e.span else none
      | _ => none
    let s := { s with sites := site.toList ++ s.sites }
    ownedExpr e s
  | .ret _ e | .throw _ e => ownedExpr e s
  | .destructure _ t dflt init => (init :: dflt.toList ++ t.defaults).foldl (fun s e => ownedExpr e s) s
  | .ite _ c t e => ownedStmts d (e.getD []) (ownedStmts d t (ownedExpr c s))
  | .loop _ c b u => ownedStmts (d + 1) u (ownedStmts (d + 1) b (ownedExpr c s))
  | .forOf _ _ _ _ i b => ownedStmts (d + 1) b (ownedExpr i s)
  -- The iterator's `close` runs where the body is left, after what of it ran.
  | .closing _ c b => ownedStmts d c (ownedStmts d b s)
  | .block _ _ b => ownedStmts d b s
  | .tryStmt _ b h f => ownedStmts d (f.getD []) (ownedStmts d ((h.map (·.2)).getD []) (ownedStmts d b s))
  | .brk .. | .cont .. => s
end

/-- The key-adding write sites of a body: the spans of the writes the
lowering may make a copy of an owned object (`ownedStmts`). In the module's
initialization, a top-level constant is a module value, which the module's
functions and classes read: it is never owned. -/
def growSites (ss : List Fragment.Stmt) (module : Bool := false) : List Span :=
  if module then
    (ss.foldl (fun s st =>
      let s := ownedStmt 0 st s
      match st with
      | .constants _ bs => { s with locals := s.locals.filter fun (n, _) => !bs.any (·.name == n) }
      | _ => s) {}).sites
  else (ownedStmts 0 ss {}).sites

end Verification.SourceExtraction
