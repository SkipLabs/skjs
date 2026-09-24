import Verification.Model.Programs.ControlFlow

/-! Bounded, untrusted evidence search. Supplied point claims are immutable.
Search fuel and the finite type vocabulary affect success, never acceptance.
The final consumer checks the actual program and exact supplied claims again. -/
namespace Verification.Model.CertificateProducer
open ProgramTyping PositiveGraphs PositiveNormalization PositiveRules
open ProgramCertificates PointClaims ControlFlow

structure PointClaim (ι : Type) where
  context : List (Ty ι)
  type : Ty ι
  deriving DecidableEq, Repr

def signature (c : NodeEvidence ι) : PointClaim ι := ⟨entry c, result c⟩

/-- Claims are part of the request, not facts the producer may replace. -/
def accept [DecidableEq ι] (G : NormalGraph ι) (R : Ty ι) (P : Program)
    (claims : List (PointClaim ι)) (C : ControlFlow.Certificate ι) (start : Nat)
    (inputs : List (Ty ι) := []) : Bool :=
  decide (C.map signature = claims) && checkEntry G R P C start inputs

theorem accept_claims [DecidableEq ι] {G : NormalGraph ι} {R P claims C start inputs}
    (hc : accept G R P claims C start inputs = true) : C.map signature = claims :=
  by
    simp only [accept, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.1

theorem accepted_safe [DecidableEq ι] {G : NormalGraph ι} {R P claims C start}
    (hc : accept G R P claims C start = true) (n : Nat) :
    SafeGraph P (meaning G R) n (ofList []) [] (.at start (fun _ => .nul)) :=
  by
    simp only [accept, Bool.and_eq_true] at hc
    exact accepted_closed_safe hc.2 n

theorem accepted_from_inputs [DecidableEq ι] {G : NormalGraph ι} {R P claims C start inputs}
    (hc : accept G R P claims C start inputs = true) (n W h ρ)
    (he : EnvOk G inputs ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafeGraph P (meaning G R) n W h (.at start ρ) := by
  simp only [accept, Bool.and_eq_true] at hc
  exact ControlFlow.accepted_inputs_safe hc.2 n W h ρ he hw hh

/-- Small arrow search: source, receiver and domain union, and pairwise
compatible codomain combination. The checker, not this search strategy,
defines the rules. -/
def arrowSearch [DecidableEq ι] (G : NormalGraph ι) (table : Table ι) (L : Ops ι)
    (S : List (Ty ι × List (Ty ι) × Ty ι × Ty ι))
    (rt : Ty ι) (c : List (Ty ι)) (d : Ty ι) : Nat → Option (PositiveCertificates.ArrowCert ι)
  | 0 => none
  | fuel+1 => Id.run do
    let basic := PositiveCertificates.ArrowCert.empty :: .emptyRecv ::
      L.map (.source ·) ++ S.map (.rest ·)
    if let some p := basic.find? (fun p => PositiveCertificates.checkArrow G table L S rt c d p) then
      return some p
    if let a :: rest := rt then
      if !rest.isEmpty then
        if let some left := arrowSearch G table L S [a] c d fuel then
          if let some right := arrowSearch G table L S rest c d fuel then
            let p := PositiveCertificates.ArrowCert.recvUnion [a] rest left right
            if PositiveCertificates.checkArrow G table L S rt c d p then return some p
    for i in List.range c.length do
      if let some (a :: rest) := c[i]? then
        if !rest.isEmpty then
          if let some left := arrowSearch G table L S rt (c.set i [a]) d fuel then
            if let some right := arrowSearch G table L S rt (c.set i rest) d fuel then
              let p := PositiveCertificates.ArrowCert.union (c.take i) [a] rest (c.drop (i+1)) left right
              if PositiveCertificates.checkArrow G table L S rt c d p then return some p
    return (L.flatMap fun p => L.map fun q =>
      PositiveCertificates.ArrowCert.combine p.2.2 q.2.2 (.source p) (.source q)).find?
        (fun p => PositiveCertificates.checkArrow G table L S rt c d p)

def arrowEvidence [DecidableEq ι] (G : NormalGraph ι) (table : Table ι)
    (pool : List (Ty ι)) : PositiveCertificates.Evidence ι :=
  let clauses := pool.flatMap (expand G)
  clauses.flatMap fun a => match a with
    | .arrs L S | .callable _ _ L S => clauses.flatMap fun b => match b with
      | .arrs M _ | .callable _ _ M _ => M.filterMap fun p =>
          (arrowSearch G table L S p.1 p.2.1 p.2.2 (p.2.1.length + p.1.length + 1)).map
            (fun proof => (L,(p,proof)))
      | _ => []
    | _ => []

/-- Delete unsupported rows of a finite candidate relation. A surviving cyclic
relation is only proposed evidence; checkCore validates every row. -/
def prune [DecidableEq ι] (G : NormalGraph ι) (pool : List (Ty ι)) :
    Nat → Table ι → Table ι
  | 0, table => table
  | fuel+1, table =>
    let es := arrowEvidence G table pool
    let next := table.filter fun p => decide (PositiveRules.Opaque G p.1 p.2) &&
      (sourceClauses G p.1).all fun a =>
      (clausesOf G p.2).any fun b => PositiveCertificates.checkClause G table es a b
    if next = table then table else prune G pool fuel next

def subtypeBase [DecidableEq ι] (G : NormalGraph ι) (pool : List (Ty ι))
    (A B : Ty ι) : Option (PositiveCertificates.Proof ι) :=
  if PositiveCertificates.check G A B .subset then some .subset else
  -- Semantic top covers every clause: one row, no arrow evidence.
  let toTop := PositiveCertificates.Proof.core ⟨[(A, B)], []⟩
  if expand G B = [.top] && PositiveCertificates.check G A B toTop then some toTop else
    let types := (A :: B :: pool).eraseDups
    let initial := types.flatMap fun a => types.map (a, ·)
    let table := prune G types initial.length initial
    let p := PositiveCertificates.Proof.core ⟨table, arrowEvidence G table types⟩
    if PositiveCertificates.check G A B p then some p else none


/-- The table built while matching, and the instances found for the
instantiated binders. -/
structure InstState (ι : Type) where
  table : InstTable ι := []
  found : Ctx ι := []

/-- Match the scheme-side type `S` against the graph's type `T` under context
`κ`, adding table entries: a parameter row to its context image, a top binder
to `T` (recorded as its instance), a row free of the context to itself, a
clause row to a clause row matched operand by operand, and a scheme row to a
scheme row, its binders standing for the other's. Untrusted: `checkInst`
validates the table. -/
def matchRow [DecidableEq ι] (G : NormalGraph ι) (bs : List ι) (V : FreeMap ι) :
    Nat → InstState ι → Ctx ι → List ι → List ι → Option (InstState ι)
  | 0, _, _, _, _ => none
  | fuel + 1, st, κ, S, T =>
    let add (st : InstState ι) (p : ι) (T : List ι) : InstState ι :=
      { st with table := (p, κ, T) :: st.table }
    let pairs (st : InstState ι) (κ : Ctx ι) (xs ys : List (List ι)) : Option (InstState ι) :=
      if xs.length = ys.length then
        (xs.zip ys).foldlM (fun st xy => matchRow G bs V fuel st κ xy.1 xy.2) st
      else none
    match S with
    | [p] =>
      match entryImg st.table κ p with
      | some U => if U = T then some st else none
      | none =>
        if G.params p then
          match κ.lookup p with
          | some U => if U = T then some (add st p T) else none
          | none =>
            if bs.contains p then
              match st.found.lookup p with
              | some U => if U = T then some st else none
              | none => some { st with found := (p, T) :: st.found }
            else if T = [p] then some (add st p T) else none
        else if T = [p] && (fv V p).all (fun q => (κ.lookup q).isNone) then some (add st p T)
        else match G.schemes p, T with
          | some s, [j] =>
            match G.schemes j with
            | some s2 =>
              if s2.binders.length = s.binders.length ∧
                  s2.signatures.length = s.signatures.length then
                let κ' := enter κ s.binders s2.binders
                (s.signatures.zip s2.signatures).foldlM (fun st pq =>
                  pairs st κ' (pq.1.1 :: pq.1.2.2 :: pq.1.2.1) (pq.2.1 :: pq.2.2.2 :: pq.2.2.1))
                  (add st p [j])
              else none
            | none => none
          | none, [j] =>
            if (G p).length = (G j).length then
              ((G p).zip (G j)).foldlM (fun st cd => pairs st κ cd.1.operands cd.2.operands)
                (add st p [j])
            else none
          | _, _ => none
    | _ =>
      if S.length = T.length then
        (S.zip T).foldlM (fun st xy => matchRow G bs V fuel st κ [xy.1] [xy.2]) st
      else none

def matchSig [DecidableEq ι] (G : NormalGraph ι) (bs : List ι) (V : FreeMap ι) (fuel : Nat)
    (st : InstState ι) (κ : Ctx ι) (p q : List ι × List (List ι) × List ι) :
    Option (InstState ι) := do
  if p.2.1.length ≠ q.2.1.length then none
  (p.1 :: p.2.2 :: p.2.1).zip (q.1 :: q.2.2 :: q.2.1) |>.foldlM
    (fun st xy => matchRow G bs V fuel st κ xy.1 xy.2) st

/-- The rows `S` reads, transitively. -/
def readsFrom [DecidableEq ι] (G : NormalGraph ι) : Nat → List ι → List ι
  | 0, S => S
  | fuel + 1, S =>
    let next := (S ++ S.flatMap (reads G)).eraseDups
    if next.length = S.length then S else readsFrom G fuel next

/-- The free parameter rows of the rows of `D`, by iteration to a fixed point:
a parameter row is free in itself, and a row has the free rows of what it
reads, except a scheme row's own binders. Untrusted: `FreeOk` checks it. -/
def freeMapOf [DecidableEq ι] (G : NormalGraph ι) (D : List ι) : Nat → FreeMap ι → FreeMap ι
  | 0, V => V
  | fuel + 1, V =>
    let step (i : ι) : List ι :=
      let bound := match G.schemes i with
        | some s => s.binders
        | none => []
      ((if G.params i then [i] else []) ++ fv V i ++
        (reads G i).flatMap fun l => (fv V l).filter (fun p => !bound.contains p)).eraseDups
    let V' := D.map fun i => (i, step i)
    if D.all (fun i => (fv V' i).length == (fv V i).length) then V' else freeMapOf G D fuel V'

/-- How far to follow a graph's rows. -/
def closureFuel : Nat := 4096

/-- The types a proof of `A ≤ B` may relate: the two, and every row they
reach. A certificate's table relates operands of their clauses, which these
are, so a pool of the whole table adds nothing but search. -/
def reachablePool [DecidableEq ι] (G : NormalGraph ι) (A B : Ty ι) : List (Ty ι) :=
  (A :: B :: (readsFrom G closureFuel (A ++ B)).map ([·])).eraseDups

/-- A scheme row below an arrow type: find the binders' instances, then build
the table under the context giving each binder its instance. -/
def instProof [DecidableEq ι] (G : NormalGraph ι) (fuel : Nat) (A B : Ty ι) :
    Option (PositiveCertificates.Proof ι) :=
  match A, expand G B with
  | [i], [.arrs L []] =>
    match G.schemes i with
    | some s => do
      let roots := s.signatures.flatMap (fun p => p.1 ++ p.2.1.flatten ++ p.2.2) ++
        L.flatMap (fun q => q.1 ++ q.2.1.flatten ++ q.2.2)
      let D := readsFrom G closureFuel roots
      let V := freeMapOf G D closureFuel []
      let first ← L.foldlM (fun st q =>
        s.signatures.findSome? fun p => matchSig G s.binders V fuel st [] p q) {}
      let θs := s.binders.map fun b => (first.found.lookup b).getD [b]
      let κ₀ := s.binders.zip θs
      let final ← L.foldlM (fun st q =>
        s.signatures.findSome? fun p => matchSig G s.binders V fuel st κ₀ p q) {}
      -- Each instance within its binder's bounds: inclusion, or a core table.
      let certs ← s.bounds.mapM fun b =>
        match κ₀.lookup b.1 with
        | none => some none
        | some U =>
          if U.all (· ∈ b.2) then some none
          else match subtypeBase G (reachablePool G U b.2) U b.2 with
            | some (.core cert) => some (some cert)
            | _ => none
      some (.inst final.table θs certs D V)
    | none => none
  | _, _ => none

/-- A type below another holding its rows' copies: each row matched, under
the empty context, against a row of the other. -/
def tableProof [DecidableEq ι] (G : NormalGraph ι) (fuel : Nat) (A B : Ty ι) :
    Option (PositiveCertificates.Proof ι) := do
  let D := readsFrom G closureFuel (A ++ B)
  let V := freeMapOf G D closureFuel []
  let st ← A.foldlM (fun st l =>
    B.findSome? fun j => matchRow G [] V fuel st [] [l] [j]) {}
  some (.table st.table D V)

/-- A type below a scheme row: a type of the pool stating the scheme's
signatures, and a proof of the inclusion in it. -/
def genProof [DecidableEq ι] (G : NormalGraph ι) (pool : List (Ty ι)) (fuel : Nat) (A B : Ty ι) :
    Option (PositiveCertificates.Proof ι) :=
  match B with
  | [j] =>
    match G.schemes j with
    | some s => do
      let U ← pool.find? fun U => expand G U == [.arrs s.signatures []]
      let p ← subtypeBase G pool A U <|> instProof G fuel A U
      let D := readsFrom G closureFuel A
      some (.gen D (freeMapOf G D closureFuel []) U p)
    | none => none
  | _ => none

/-- A proof of `A ≤ B`: structural, by instantiating a scheme row, or by
generalizing to one. Every proposal is checked. -/
def subtype [DecidableEq ι] (G : NormalGraph ι) (pool : List (Ty ι))
    (A B : Ty ι) : Option (PositiveCertificates.Proof ι) :=
  let fuel := 64 + pool.length
  let ok p := PositiveCertificates.check G A B p
  (subtypeBase G pool A B) <|> ((instProof G fuel A B).filter ok) <|>
    ((genProof G pool fuel A B).filter ok) <|> ((tableProof G fuel A B).filter ok)
def coerce [DecidableEq ι] (G : NormalGraph ι) (pool : List (Ty ι))
    (e : ProgramCertificates.Evidence ι) (A : Ty ι) : Option (ProgramCertificates.Evidence ι) := do
  if (claim e).type = A then return e
  let p ← subtype G pool (claim e).type A
  return .node ⟨(claim e).context, (claim e).term, A⟩ (.sub p) [e]

instance [DecidableEq ι] (G : NormalGraph ι) (B : Ty ι) (tag : Tag) (q : Bool) :
    Decidable (Answers G B tag q) := by unfold Answers; infer_instance

/-- Search ordinary typing rules. Every recursive expression request decreases
search fuel, including implicit let typing. Suggestions only prioritize candidate
types; every premise is proved in the actual context, even when the suggestion
came from a different context. No execution budget is inspected. -/
def expressionWith [DecidableEq ι] (G : NormalGraph ι) (pool : List (Ty ι))
    (suggestions : List (Sequent ι)) :
    Nat → List (Ty ι) → Tm → Ty ι → Option (ProgramCertificates.Evidence ι)
  | 0, _, _, _ => none
  | fuel+1, Γ, t, A => Id.run do
    let leaf := fun B r => ProgramCertificates.Evidence.node ⟨Γ,t,B⟩ r []
    let recur := expressionWith G pool suggestions fuel
    -- Union elimination refines an immutable receiver slot in each premise;
    -- it neither evaluates the operation twice nor inserts a runtime tag test.
    let splitReceiver := fun receiver => do
      let .var i := receiver | none
      let B ← Γ[i]?
      if B.length ≤ 1 then none else do
        let ps ← B.mapM fun b => recur (Γ.set i [b]) t A
        pure (ProgramCertificates.Evidence.node ⟨Γ,t,A⟩ (.unionVar i) ps)
    match t with
    | .var i => return (Γ[i]?).bind fun B => coerce G pool (leaf B .var) A
    | .nul | .undef | .tru | .fls =>
      let r := match t with | .nul => Rule.nul | .undef => .undef | .tru => .tru | _ => .fls
      return (A :: pool).findSome? fun B =>
        let r := if expand G B = [.boolLit true] && t == .tru then Rule.truLit
          else if expand G B = [.boolLit false] && t == .fls then Rule.flsLit else r
        if checkTree G (leaf B r) then coerce G pool (leaf B r) A else none
    -- A number has one rule: its own singleton. Reaching `number`, or any
    -- union above it, is the coercion's job, exactly as for a boolean literal.
    | .num _ =>
      -- Its own singleton where the claim names one, the family where it does
      -- not: a literal claimed at `number` has no singleton label to coerce
      -- from, exactly as a Boolean claimed at `boolean` has none.
      return (A :: pool).findSome? fun B =>
        if checkTree G (leaf B .numLit) then coerce G pool (leaf B .numLit) A
        else if checkTree G (leaf B .num) then coerce G pool (leaf B .num) A
        else none
    | .str _ =>
      return (A :: pool).findSome? fun B =>
        if checkTree G (leaf B .strLit) then coerce G pool (leaf B .strLit) A
        else if checkTree G (leaf B .str) then coerce G pool (leaf B .str) A
        else none
    | .make (.closure arity b) .nul =>
      return (A :: pool).findSome? fun F => do
        match expand G F with
        | [.arrs L []] =>
          if !L.all (fun p => p.2.1.length == arity) then none else do
          let ps ← L.mapM fun p => recur (p.1 :: p.2.1 ++ Γ) b p.2.2
          coerce G pool (.node ⟨Γ,t,F⟩ .funE ps) A
        | [.callable P [] L []] =>
          if !L.all (fun p => p.2.1.length == arity) then none else do
          let [(_, Pv)] := P | none
          let ea ← recur Γ .nul Pv
          let ps ← L.mapM fun p => recur (p.1 :: p.2.1 ++ Γ) b p.2.2
          coerce G pool (.node ⟨Γ,t,F⟩ .makeCallable (ea :: ps)) A
        | _ => none
    -- A class value: one body per construct signature, its receiver slot at
    -- a pool type that is exactly `undefined`, what `new` passes there.
    | .make (.closure arity b .construct) .nul =>
      return (A :: pool).findSome? fun F => do
        let [.ctors L] := expand G F | none
        if !L.all (fun p => p.1.length == arity) then none else do
        let U ← pool.find? fun U => decide (expand G U = [.undef])
        let ps ← L.mapM fun p => recur (U :: p.1 ++ Γ) b p.2
        coerce G pool (.node ⟨Γ,t,F⟩ (.ctorE U) ps) A
    -- `new f(args)`: a construct signature of the constructor's type taking as
    -- many parameters as there are actuals.
    | .construct f args =>
      return pool.findSome? fun F => do
        let [.ctors L] := expand G F | none
        L.findSome? fun p => do
          if args.length != p.1.length then none else do
          let _ ← subtype G pool p.2 A
          let ef ← recur Γ f F
          let eas ← (args.zip p.1).mapM fun (a,D) => recur Γ a D
          coerce G pool (.node ⟨Γ,t,p.2⟩ .construct (ef :: eas)) A
    -- A variadic closure: one body premise per signature, the body's slot 0
    -- at a pool type that is that signature's rest array.
    | .make (.variadic arity b) .nul =>
      return (A :: pool).findSome? fun F => do
        let [.arrs [] L] := expand G F | none
        if !L.all (fun p => p.2.1.length == arity) then none else do
        let arrays ← L.mapM fun p => pool.find? fun R => decide (RestArray G R p.2.2.1)
        let ps ← (L.zip arrays).mapM fun (p, R) => recur (R :: p.1 :: p.2.1 ++ Γ) b p.2.2.2
        coerce G pool (.node ⟨Γ,t,F⟩ (.funRest arrays) ps) A
    -- A variadic callable object: the bag's initializers, then one body per
    -- signature with its rest array in slot 0.
    | .makeAt (.variadic arity b) ns inits =>
      return (A :: pool).findSome? fun F => do
        let [.callable P [] [] L] := expand G F | none
        if !L.all (fun p => p.2.1.length == arity) then none else do
        if P.map Prod.fst != ns || inits.length != ns.length then none else do
        let eas ← (inits.zip (P.map Prod.snd)).mapM fun (a,D) => recur Γ a D
        let arrays ← L.mapM fun p => pool.find? fun R => decide (RestArray G R p.2.2.1)
        let ps ← (L.zip arrays).mapM fun (p, R) => recur (R :: p.1 :: p.2.1 ++ Γ) b p.2.2.2
        coerce G pool (.node ⟨Γ,t,F⟩ (.makeCallableRest arrays) (eas ++ ps)) A
    | .makeAt (.closure arity b) ns inits =>
      return (A :: pool).findSome? fun F => do
        let [.callable P [] L []] := expand G F | none
        if !L.all (fun p => p.2.1.length == arity) then none else do
        if P.map Prod.fst != ns || inits.length != ns.length then none else do
        let eas ← (inits.zip (P.map Prod.snd)).mapM fun (a,D) => recur Γ a D
        let ps ← L.mapM fun p => recur (p.1 :: p.2.1 ++ Γ) b p.2.2
        coerce G pool (.node ⟨Γ,t,F⟩ .makeCallable (eas ++ ps)) A
    -- `.bind`'s forwarding descriptor: a leaf whose checker reads the saved
    -- slots from the context; the claimed type, or a pool type, is its result.
    | .makeAt (.bound (.var _) (.var _) _) [] [] =>
      return (A :: pool).findSome? fun F =>
        if checkTree G (leaf F .bindE) then coerce G pool (leaf F .bindE) A
        else if checkTree G (leaf F .bindRestE) then coerce G pool (leaf F .bindRestE) A
        else none
    | .letE a b =>
      let exactTypes := suggestions.reverse.filterMap fun j =>
        if j.context == Γ && j.term == a then some j.type else none
      let termTypes := suggestions.reverse.filterMap fun j =>
        if j.term == a then some j.type else none
      let variableType := match a with | .var i => (Γ[i]?).toList | _ => []
      let preferred := variableType ++ exactTypes ++ termTypes
      return (preferred ++ pool).eraseDups.findSome? (fun B => do
        let ea ← recur Γ a B
        let eb ← recur (B :: Γ) b A
        return ProgramCertificates.Evidence.node ⟨Γ,t,A⟩ .letE [ea,eb])
    | .invoke f recv args =>
      -- A variadic callee: the receiver at the signature's receiver, the fixed
      -- actuals at its parameters, then each part at its element type, or a
      -- spread of a pool store type whose elements are.
      let variadic := pool.findSome? fun F => do
        (restSigs G F).findSome? fun (Rt, Ps, E, B) => do
          -- Fixed actuals first; a shorter call omits trailing fixed positions,
          -- each proving `undefined`, and writes no further part.
          let k := min args.length Ps.length
          let omitted := Ps.drop k
          let parts := args.drop k
          if !omitted.isEmpty && !parts.isEmpty then none else do
          let _ ← subtype G pool B A
          let ef ← recur Γ f F
          let er ← recur Γ recv Rt
          let eas ← (args.zip Ps).mapM fun (a,D) => recur Γ a D
          let eus ← omitted.mapM fun D => recur Γ .undef D
          let eps ← parts.mapM fun a => match a with
            | .spread s => pool.findSome? fun S =>
                if decide (SpreadsInto G S E) then recur Γ s S else none
            | a => recur Γ a E
          let flags := parts.map fun a => match a with | .spread _ => true | _ => false
          let e := ProgramCertificates.Evidence.node ⟨Γ,t,B⟩
            (.callRest k omitted.length flags E) (ef :: er :: eas ++ eus ++ eps)
          if checkTree G e then coerce G pool e A else none
      if let some e := variadic then return some e
      let direct := pool.findSome? fun F => do
        let (L,r) ← match expand G F with
          | [.arrs L _] => some (L,Rule.app)
          | [.callable _ _ L _] => some (L,Rule.callCallable)
          | _ => none
        L.findSome? fun p => do
          -- Require every operand before searching the premises. A signature
          -- with more positions than the call writes is usable when each
          -- remaining contract admits `undefined`, the value bound there.
          if args.length > p.2.1.length then none else do
            let omitted := p.2.1.drop args.length
            let _ ← subtype G pool p.2.2 A
            let ef ← recur Γ f F
            let er ← recur Γ recv p.1
            let eas ← (args.zip p.2.1).mapM fun (a,D) => recur Γ a D
            let eus ← omitted.mapM fun D => recur Γ .undef D
            coerce G pool (.node ⟨Γ,t,p.2.2⟩ r (ef :: er :: eas ++ eus)) A
      if let some e := direct then return some e
      return splitReceiver f
    | .makeAt .absent ns inits =>
      return (A :: pool).findSome? fun R => do
        if !(decide ns.Nodup) then none else do
        if inits.length != ns.length then none else do
        match expand G R with
        | [.refs B [] []] =>
          if B.map Prod.fst != ns then none else do
          let ps ← (inits.zip (B.map Prod.snd)).mapM fun (a,D) => recur Γ a D
          coerce G pool (.node ⟨Γ,t,R⟩ .alloc ps) A
        | [.dict [] [] [] [E]] =>
          let ps ← inits.mapM fun a => recur Γ a E
          coerce G pool (.node ⟨Γ,t,R⟩ .allocDict ps) A
        | _ => none
    | .indexAt a key =>
      return (A :: pool).findSome? fun R => do
        let [.dict _ [] _ (E :: _)] := expand G R | none
        (A :: pool).findSome? fun K => do
          if expand G K != [.str] then none else do
          (A :: pool).findSome? fun U => do
            if expand G U != [.undef] then none else do
            let B := E ++ U
            let _ ← subtype G pool B A
            let ea ← recur Γ a R
            let ek ← recur Γ key K
            coerce G pool (.node ⟨Γ,t,B⟩ (.indexDict E U) [ea, ek]) A
    | .readAt f a =>
      let direct := pool.findSome? fun R => do
        -- An invariant field reads at its contract; a view field at its bound;
        -- an optional field at its contract or `undefined`.
        let (B,r) ← match expand G R with
          | [.refs fs [] vs os] =>
            (fs.lookup f).map (·,Rule.read) <|> (vs.lookup f).map (·,Rule.readView) <|>
              (os.lookup f).bind fun E => pool.findSome? fun U =>
                if expand G U == [.undef] then some (E ++ U, Rule.readOptional E U) else none
          | [.callable fs _ _ _] => (fs.lookup f).map (·,Rule.readCallable)
          | [.dict _ [] _ (B :: _)] =>
            pool.findSome? fun U =>
              if expand G U == [.undef] then some (B ++ U, Rule.readDict B U) else none
          | _ => none
        let _ ← subtype G pool B A
        let ea ← recur Γ a R
        coerce G pool (.node ⟨Γ,t,B⟩ r [ea]) A
      if let some e := direct then return some e
      return splitReceiver a
    | .writeAt f a b =>
      let direct := pool.findSome? fun R => do
        let (fs,r) ← match expand G R with
          | [.refs fs [] _ _] => some (fs,Rule.write)
          | [.callable fs _ _ _] => some (fs,Rule.writeCallable)
          | _ => none
        let B ← fs.lookup f
        let ea ← recur Γ a R
        let eb ← recur Γ b B
        (A :: pool).findSome? fun N =>
          let e := ProgramCertificates.Evidence.node ⟨Γ,t,N⟩ r [ea,eb]
          if checkTree G e then coerce G pool e A else none
      if let some e := direct then return some e
      return splitReceiver a
    | .arith _ a b =>
      -- Each operand at a pool type the number test answers for; the result
      -- at the requested type when it is the number family, else coerced.
      let numbers := pool.filter fun R => decide (Answers G R .isNum true)
      return numbers.findSome? fun R => do
        let ea ← recur Γ a R
        numbers.findSome? fun S => do
          let eb ← recur Γ b S
          (A :: pool).findSome? fun N =>
            let e := ProgramCertificates.Evidence.node ⟨Γ,t,N⟩ .arith [ea,eb]
            if checkTree G e then coerce G pool e A else none
    -- A copy of a spread: a store type of any length at some element type,
    -- and a pool store type whose elements it admits.
    | .arrLit [.spread src] =>
      return (A :: pool).findSome? fun L => do
        let [.list ⟨[], [], some E, false⟩ []] := expand G L | none
        pool.findSome? fun S => do
          if !decide (SpreadsInto G S E) then none else do
          let es ← recur Γ src S
          coerce G pool (.node ⟨Γ,t,L⟩ (.arrCopy E) [es]) A
    | .arrLit inits =>
      -- The claimed type, or a pool type, names the tuple; each initializer
      -- is typed at its position's contract.
      return (A :: pool).findSome? fun L => do
        let [.list T []] := expand G L | none
        if inits.length < T.required.length then none else
        if T.rest.isNone && T.required.length + T.optional.length < inits.length then none else do
        let ps ← inits.zipIdx.mapM fun (a, k) => do
          let B ← positionTy T k
          recur Γ a B
        let e := ProgramCertificates.Evidence.node ⟨Γ,t,L⟩ .arrLit ps
        if checkTree G e then coerce G pool e A else none
    | .elemAt a i =>
      -- A store read through a union of array objects splits the receiver.
      let direct := pool.findSome? fun L => do
        let [.list T []] := expand G L | none
        let ea ← recur Γ a L
        pool.findSome? fun I => do
          let ei ← recur Γ i I
          match expand G I with
          | [.numLit b] => do
            let k ← indexOfBits b
            match T.required[k]? with
            | some B => coerce G pool (.node ⟨Γ,t,B⟩ .elem [ea,ei]) A
            | none => do
              let B ← positionTy T k
              (A :: pool).findSome? fun U =>
                let e := ProgramCertificates.Evidence.node ⟨Γ,t,B ++ U⟩ (.elemOpt U) [ea,ei]
                if checkTree G e then coerce G pool e A else none
          | _ =>
            match T with
            | ⟨[], [], some E, false⟩ =>
              (A :: pool).findSome? fun U =>
                let e := ProgramCertificates.Evidence.node ⟨Γ,t,E ++ U⟩ (.elemAny U) [ea,ei]
                if checkTree G e then coerce G pool e A else none
            | _ => none
      if let some e := direct then return some e
      let .readAt _ receiver := a | return none
      return splitReceiver receiver
    | .setElem a i v =>
      return pool.findSome? fun L => do
        let [.list T []] := expand G L | none
        let ea ← recur Γ a L
        pool.findSome? fun I => do
          let [.numLit b] := expand G I | none
          let ei ← recur Γ i I
          let k ← indexOfBits b
          let B ← positionTy T k
          let ev ← recur Γ v B
          let e := ProgramCertificates.Evidence.node ⟨Γ,t,L⟩ .setElem [ea,ei,ev]
          if checkTree G e then coerce G pool e A else none
    | .lenOf a =>
      return pool.findSome? fun L => do
        let [.list _ []] := expand G L | none
        let ea ← recur Γ a L
        (A :: pool).findSome? fun N =>
          let e := ProgramCertificates.Evidence.node ⟨Γ,t,N⟩ .len [ea]
          if checkTree G e then coerce G pool e A else none
    | .ite (.test tag (.var i)) u e =>
      let some B := Γ[i]? | return none
      if decide (Answers G B tag true) then
        return (recur Γ u A).map fun p => .node ⟨Γ,t,A⟩ .ifTrue [p]
      if decide (Answers G B tag false) then
        return (recur Γ e A).map fun p => .node ⟨Γ,t,A⟩ .ifFalse [p]
      -- Split only an explicit union. A singleton whose graph clause itself
      -- mixes shapes is not made smaller by repeating this rule; its answer
      -- is unknown, the test is a Boolean, and both arms are typed.
      if B.length ≤ 1 then
        return (A :: pool).findSome? fun C => do
          if !decide ((.boolLit true) ∈ expand G C ∧ (.boolLit false) ∈ expand G C) then none else do
          let pc := ProgramCertificates.Evidence.node ⟨Γ,.test tag (.var i),C⟩ .test
            [.node ⟨Γ,.var i,B⟩ .var []]
          let pt ← recur Γ u A
          let pe ← recur Γ e A
          pure (.node ⟨Γ,t,A⟩ .ifBool [pc,pt,pe])
      return do
        let ps ← B.mapM fun a => recur (Γ.set i [a]) t A
        pure (.node ⟨Γ,t,A⟩ (.unionVar i) ps)
    | .ite c t e =>
      let known := pool.findSome? fun C => do
        let [.boolLit q] := expand G C | none
        let pc ← recur Γ c C
        let pb ← recur Γ (if q then t else e) A
        pure (.node ⟨Γ,.ite c t e,A⟩ (.ifKnown q) [pc,pb])
      if let some p := known then return some p
      let refined := do
        let .var i := c | none
        let C ← Γ[i]?
        if !decide (Answers G C .isBool true) then none else do
          let T ← pool.find? fun T => decide (expand G T = [.boolLit true])
          let F ← pool.find? fun F => decide (expand G F = [.boolLit false])
          let pt ← recur (Γ.set i T) t A
          let pe ← recur (Γ.set i F) e A
          pure (.node ⟨Γ,.ite c t e,A⟩ (.ifBoolVar T F) [pt,pe])
      if let some p := refined then return some p
      return pool.findSome? fun C => do
        if !decide (Answers G C .isBool true) then none else do
          let pc ← recur Γ c C
          let pt ← recur Γ t A
          let pe ← recur Γ e A
          pure (.node ⟨Γ,.ite c t e,A⟩ .ifBool [pc,pt,pe])
    | _ => return none

/-- Raw calculus callers need not supply source-derived search suggestions. -/
def expression [DecidableEq ι] (G : NormalGraph ι) (pool : List (Ty ι)) :=
  expressionWith G pool []

/-- Gather graph labels, recursive operands and supplied union types. Hints may
add intermediate types; they cannot change claims or bypass evidence checking. -/
def vocabulary [DecidableEq ι] (G : NormalGraph ι) (labels : List ι)
    (claims : List (PointClaim ι)) (hints : List (Ty ι)) : List (Ty ι) :=
  ([] :: (labels.map fun i => [i]) ++ hints ++
    claims.flatMap (fun c => c.type :: c.context) ++
    labels.flatMap (fun i => (G i).flatMap fun c => match c with
      | .refs A bs vs => A.map Prod.snd ++ bs.flatMap (·.map Prod.snd) ++ vs.map Prod.snd
      | .list a bs => (a :: bs).flatMap fun t => t.required ++ t.optional ++ t.rest.toList
      | .arrs L S => L.flatMap (fun p => p.1 :: p.2.1 ++ [p.2.2]) ++
          S.flatMap (fun p => p.1 :: p.2.1 ++ [p.2.2.1, p.2.2.2])
      | .callable A bs L S =>
          A.map Prod.snd ++ bs.flatMap (·.map Prod.snd) ++ L.flatMap (fun p => p.1 :: p.2.1 ++ [p.2.2]) ++
            S.flatMap (fun p => p.1 :: p.2.1 ++ [p.2.2.1, p.2.2.2])
      | _ => [])).eraseDups

inductive Failure where
  | claimCount
  | expression (label : Nat)
  | edge (source : Nat) (destination : Nat) (edgeIndex : Nat)
  | rejected
  deriving DecidableEq, Repr

/-- Ordinary and observed edges share slot selection and coverage search. The
observation comes from graph dispatch, never from supplied point annotations. -/
def edge [DecidableEq ι] (G : NormalGraph ι) (pool : List (Ty ι))
    (claims : List (PointClaim ι)) (Γ : List (Ty ι)) (target : Target)
    (observed : Option (Nat × BranchRefinement.Observation) := none) :
    Option (EdgeEvidence ι) := do
  let c ← claims[target.label]?
  if let some (tested, _) := observed then
    if Γ[tested]?.isNone then failure
  if let some slots := target.mapping then
    if slots.length != c.context.length then failure
  (List.range c.context.length).mapM fun i => do
    let A ← Γ[slot target.mapping i]?
    let B ← c.context[i]?
    match observed with
    | some (tested, o) =>
      if slot target.mapping i == tested then
        match o with
        | .boolean q =>
          if BranchRefinement.booleanMember G B q then pure .subset else failure
        | .tag t q => subtype G pool (BranchRefinement.tagSlice G A t q) B
      else subtype G pool A B
    | none => subtype G pool A B


/-- Select effect evidence without changing the requested sequent. A precise
read/value rule may succeed when ordinary derivation search cannot. -/
def expressionEffect [DecidableEq ι] (G : NormalGraph ι) (pool : List (Ty ι))
    (fuel : Nat) (j : Sequent ι) (k : HeapKnowledge.Knowledge)
    (suggestions : List (Sequent ι)) (known : List (Evidence ι)) :
    Option (Evidence ι × HeapExpressionRules.StepEvidence ι × HeapKnowledge.Knowledge) := Id.run do
  let ordinary := (known.find? fun e => claim e == j).orElse fun _ =>
    expressionWith G pool suggestions fuel j.context j.term j.type
  let mut choices : List (HeapExpressionRules.StepEvidence ι) := []
  match j.term with
  | .var i =>
    if let some R := HeapExpressionRules.valuesAt G j.context k i then
      choices := [.knownValue i R]
  | .readAt fld (.var i) =>
    choices := (k.cells.filter fun f => f.slot == i && f.field == fld).map
      fun f => .observedRead i f.contents
  | _ => pure ()
  if let some e := ordinary then
    match j.term with
    | .readAt _ (.var i) =>
      if let some Ref := j.context[i]? then
        if let some B := HeapExpressionRules.bagOperand (expand G Ref) then
          choices := choices ++ [.typedRead i B e]
    | .makeAt .. =>
      choices := choices ++ [.allocated e]
    | .writeAt _ (.var i) (.var v) =>
      if let some R := HeapExpressionRules.valuesAt G j.context k v then
        choices := choices ++ [.written i v R e]
    | _ => pure ()
    choices := choices ++ [.created e,.pure e,.ordinary e]
  for effect in choices do
    if let some out := HeapExpressionRules.checkStep G j k effect then
      -- Effect evidence validates this header itself; an ordinary derivation
      -- is not required for the precise read/value alternatives.
      return some (ordinary.getD (.node j .var []),effect,out)
  return none

/-- All predecessor edges come from executable continuations. -/
def successors : Continuation → List Target
  | .ret => []
  | .bind t | .effect t => [t]
  | .branch y n | .branchBind y n | .tagBind _ y n => [y,n]

def edgeKnowledge (k : HeapKnowledge.Knowledge) (cont : Continuation) (index : Nat) :
    HeapKnowledge.Knowledge :=
  match cont with
  | .effect _ | .branch _ _ => HeapKnowledge.dropResult k
  | .branchBind _ _ => HeapKnowledge.observe k 0 (.boolean (index == 0))
  | .tagBind t _ _ => HeapKnowledge.observe k 0 (.tag t (index == 0))
  | _ => k

private def produceNode [DecidableEq ι] (G : NormalGraph ι) (pool : List (Ty ι))
    (fuel l : Nat) (node : Node) (claims : List (PointClaim ι))
    (k : HeapKnowledge.Knowledge) (suggestions : List (Sequent ι)) (known : List (Evidence ι)) :
    Except Failure (NodeEvidence ι) := do
  let some c := claims[l]? | throw .claimCount
  let some (e,effect,out) := expressionEffect G pool fuel ⟨c.context,node.expression,c.type⟩ k suggestions known
    | throw (.expression l)
  let target := fun Γ t index => match edge G pool claims Γ t with
    | some p => Except.ok p
    | none => Except.error (Failure.edge l t.label index)
  let branchTarget := fun Γ o t index => match edge G pool claims Γ t (some (0, o)) with
    | some p => Except.ok p
    | none => Except.error (Failure.edge l t.label index)
  let ps ← (match node.continuation with
    | .ret => pure []
    | .bind t => (target (c.type :: c.context) t 0).map (fun p => [p])
    | .effect t => (target c.context t 0).map (fun p => [p])
    | .branch y n => (target c.context y 0).bind (fun py =>
        (target c.context n 1).map (fun pn => [py,pn]))
    | .branchBind y n => (branchTarget (c.type :: c.context) (.boolean true) y 0).bind (fun py =>
        (branchTarget (c.type :: c.context) (.boolean false) n 1).map (fun pn => [py,pn]))
    | .tagBind t y n => (branchTarget (c.type :: c.context) (.tag t true) y 0).bind (fun py =>
        (branchTarget (c.type :: c.context) (.tag t false) n 1).map (fun pn => [py,pn])) : Except Failure (List (EdgeEvidence ι)))
  return {expression := e, edges := ps, knowledge := k, effect := some effect, output := out}

/-- Propagate established postconditions along single-predecessor paths. Entry
starts empty; source cuts use exactly their supplied requirements, even when
empty. Other merge points use supplied requirements. A node is checked once
when its unique predecessor is available; this is dependency scheduling, not invariant iteration.
Every edge is still checked by the independent consumer. -/
def produceRaw [DecidableEq ι] (G : NormalGraph ι) (pool : List (Ty ι))
    (fuel : Nat) (P : Program) (claims : List (PointClaim ι))
    (suggestions : List (Sequent ι) := []) (known : List (Evidence ι) := []) (start : Nat := 0)
    (requirements : List (Nat × HeapKnowledge.Knowledge) := []) (cuts : List Nat := []) :
    Except Failure (ControlFlow.Certificate ι) := do
  if P.length != claims.length then throw .claimCount
  let incoming := (List.range P.length).map fun target =>
    P.zipIdx.flatMap fun (node,l) =>
      (successors node.continuation).zipIdx.filterMap fun (t,index) =>
        if t.label == target then some (l,index,t) else none
  let mut table : List (Option (NodeEvidence ι)) := List.replicate P.length none
  -- A merge waits for its predecessors while some pass still makes progress;
  -- once none does, the merges still waiting (a cycle through no cut) take
  -- their stated requirements alone, as every merge did before.
  let mut force := false
  for _ in List.range (2 * P.length + 2) do
    let mut progress := false
    for l in List.range P.length do
      if ((table[l]?).getD none).isSome then continue
      let some node := P[l]? | throw .claimCount
      let some c := claims[l]? | throw .claimCount
      let required := (requirements.lookup l).getD ⟨[],[],[]⟩
      let mut k := required
      if l != start && !cuts.contains l then
        match incoming[l]? with
        | some [(pred,index,target)] =>
          let some previous := (table[pred]?).getD none | continue
          let some source := P[pred]? | throw .claimCount
          k := HeapKnowledge.project (edgeKnowledge previous.output source.continuation index)
            target.mapping c.context.length
        | some preds =>
          -- A merge that is not a cut states no requirement of its own; it
          -- keeps what every predecessor establishes, once all are available.
          -- Cycles pass through cuts, so waiting here cannot deadlock.
          let mut projections : List HeapKnowledge.Knowledge := []
          let mut ready := true
          for (pred,index,target) in preds do
            match (table[pred]?).getD none, P[pred]? with
            | some previous, some source =>
              projections := projections ++ [HeapKnowledge.project
                (edgeKnowledge previous.output source.continuation index) target.mapping c.context.length]
            | _, _ => ready := false
          if !ready && !force then continue
          if ready then k := HeapKnowledge.meet projections
        | none => pure ()
      k := ⟨(k.cells ++ required.cells).eraseDups,(k.values ++ required.values).eraseDups,
        (k.links ++ required.links).eraseDups⟩
      let evidence ← produceNode G pool fuel l node claims k suggestions known
      table := table.set l (some evidence)
      progress := true
    if !progress then
      if force then break else force := true
    else force := false
  table.mapM fun c => match c with
    | some e => pure e
    | none => throw .rejected

/-- Recover a located failed edge from the completed candidate. This includes
heap entailment; it is not limited to ordinary subtype proof construction. -/
private def failedEdge (P : Program)
    (C : ControlFlow.Certificate ι) : Option Failure := Id.run do
  for (node,l) in P.zipIdx do
    let some c := C[l]? | return some .claimCount
    for (target,index) in (successors node.continuation).zipIdx do
      let facts := edgeKnowledge c.output node.continuation index
      let some destination := C[target.label]? | return some .claimCount
      if !HeapKnowledge.check facts destination.knowledge target.mapping then
        return some (.edge l target.label index)
  return none

def produce [DecidableEq ι] (G : NormalGraph ι) (labels : List ι)
    (fuel : Nat) (R : Ty ι) (P : Program) (claims : List (PointClaim ι))
    (start : Nat) (hints : List (Ty ι) := []) (inputs : List (Ty ι) := [])
    (suggestions : List (Sequent ι) := []) (known : List (ProgramCertificates.Evidence ι) := [])
    (requirements : List (Nat × HeapKnowledge.Knowledge) := []) (cuts : List Nat := []) : Except Failure (ControlFlow.Certificate ι) :=
  match produceRaw G (vocabulary G labels claims (inputs ++ hints)) fuel P claims suggestions known start requirements cuts with
  | .error e => .error e
  | .ok C => if accept G R P claims C start inputs then .ok C
    else .error ((failedEdge P C).getD .rejected)

theorem produce_checked [DecidableEq ι] {G : NormalGraph ι} {labels fuel R P claims start hints inputs suggestions known requirements cuts C}
    (h : produce G labels fuel R P claims start hints inputs suggestions known requirements cuts = .ok C) :
    accept G R P claims C start inputs = true := by
  unfold produce at h
  split at h
  · contradiction
  · split at h
    · cases h; assumption
    · contradiction

#print axioms accepted_from_inputs
#print axioms accepted_safe
#print axioms produce_checked
end Verification.Model.CertificateProducer
