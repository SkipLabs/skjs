import Verification.Model.Programs.ControlFlow

/-! Bounded, untrusted evidence search. Supplied point claims are immutable.
Search fuel and the finite type vocabulary affect success, never acceptance.
The final consumer checks the actual program and exact supplied claims again. -/
namespace Verification.Model.CertificateProducer
open ProgramTyping PositiveGraphs PositiveNormalization PositiveRules
open ProgramCertificates PointClaims ControlFlow
open CallEffects (Arrow RestArrow Contract Effect)
open PositiveCertificates (InstanceImageCheck finiteInstanceImages)

structure PointClaim (ι : Type) where
  context : List (Ty ι)
  type : Ty ι
  deriving DecidableEq, Repr

def signature (c : NodeEvidence ι) : PointClaim ι := ⟨entry c, result c⟩

/-- Claims are part of the request, not facts the producer may replace. -/
def acceptUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (R : Ty ι) (P : Program)
    (claims : List (PointClaim ι)) (C : ControlFlow.Certificate ι) (start : Nat)
    (inputs : List (Ty ι) := []) (codes : CodeEntry ι → Bool := fun _ => false) : Bool :=
  decide (C.map signature = claims) && checkEntryUsing G images R P C start inputs codes

theorem accept_claims [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {R P claims C start inputs codes}
    (hc : acceptUsing G images R P claims C start inputs codes = true) : C.map signature = claims :=
  by
    simp only [acceptUsing, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.1

theorem accepted_safe [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {R P claims C start}
    (hc : acceptUsing G images R P claims C start = true) (n : Nat) :
    SafeGraph P (meaning G R) n (ofList []) [] (.at start (fun _ => .nul)) :=
  by
    simp only [acceptUsing, Bool.and_eq_true] at hc
    exact accepted_closed_safe hc.2 n

theorem accepted_from_inputs [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {R P claims C start inputs}
    {codes : CodeEntry ι → Bool} (hc : acceptUsing G images R P claims C start inputs codes = true) (n W h ρ)
    (he : EnvOk G inputs ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h)
    (hcodes : ProgramCertificates.CodesSound G codes := by exact Verification.Model.ProgramCertificates.codesSound_none _) :
    SafeGraph P (meaning G R) n W h (.at start ρ) := by
  simp only [acceptUsing, Bool.and_eq_true] at hc
  exact ControlFlow.accepted_inputs_safe hc.2 n W h ρ he hw hh hcodes

/-- Small arrow search: source, receiver and domain union, and pairwise
compatible codomain combination. The checker, not this search strategy,
defines the rules. -/
def arrowSearch [DecidableEq ι] (G : NormalGraph ι) (table : Table ι) (L : Ops ι)
    (S : List (RestArrow (Ty ι)))
    (q : Arrow (Ty ι)) : Nat → Option (PositiveCertificates.ArrowCert ι)
  | 0 => none
  | fuel+1 => Id.run do
    let basic := PositiveCertificates.ArrowCert.empty :: .emptyRecv ::
      L.map (.source ·) ++ S.map (.rest ·)
    if let some p := basic.find? (fun p => PositiveCertificates.checkArrow G table L S q p) then
      return some p
    if let a :: rest := q.receiver then
      if !rest.isEmpty then
        if let some left := arrowSearch G table L S {q with receiver := [a]} fuel then
          if let some right := arrowSearch G table L S {q with receiver := rest} fuel then
            let p := PositiveCertificates.ArrowCert.recvUnion [a] rest left right
            if PositiveCertificates.checkArrow G table L S q p then return some p
    for i in List.range q.arguments.length do
      if let some (a :: rest) := q.arguments[i]? then
        if !rest.isEmpty then
          if let some left := arrowSearch G table L S {q with arguments := q.arguments.set i [a]} fuel then
            if let some right := arrowSearch G table L S {q with arguments := q.arguments.set i rest} fuel then
              let p := PositiveCertificates.ArrowCert.union (q.arguments.take i) [a] rest (q.arguments.drop (i+1)) left right
              if PositiveCertificates.checkArrow G table L S q p then return some p
    return (L.flatMap fun p => L.map fun q =>
      PositiveCertificates.ArrowCert.combine p.result q.result p.effect q.effect (.source p) (.source q)).find?
        (fun p => PositiveCertificates.checkArrow G table L S q p)

def arrowEvidence [DecidableEq ι] (G : NormalGraph ι) (table : Table ι)
    (pool : List (Ty ι)) : PositiveCertificates.Evidence ι :=
  let clauses := pool.flatMap (expand G)
  let arrows (L : Ops ι) (S : List (RestArrow (Ty ι))) (M : Ops ι) :=
    M.filterMap fun p =>
      (arrowSearch G table L S p (p.arguments.length + p.receiver.length + 1)).map
        (fun proof => (L,(p,proof)))
  -- A scheme row's signatures are compared as an arrow clause's, against
  -- those of a scheme binding the same rows that a row of the table relates
  -- it to (`SchemeCoversWith`).
  let schemeRow (i : ι) : Bool := (G.schemes i).isSome
  let schemes := ((table.filter fun r => r.1.any schemeRow && r.2.any schemeRow).flatMap fun r =>
    r.1.flatMap fun i => r.2.filterMap fun j =>
      if i ∈ r.2 then none else match G.schemes i, G.schemes j with
        | some s, some s' => if s.binders = s'.binders then some (s, s') else none
        | _, _ => none).eraseDups
  (clauses.flatMap fun a => match a with
    | .arrs L S | .callable _ _ L S => clauses.flatMap fun b => match b with
      | .arrs M _ | .callable _ _ M _ => arrows L S M
      | _ => []
    | _ => []) ++
  schemes.flatMap fun (s, s') => arrows s.signatures s.variadic s'.signatures

/-- Delete unsupported rows of a finite candidate relation. A surviving cyclic
relation is only proposed evidence; checkCore validates every row. -/
def prune [DecidableEq ι] (G : NormalGraph ι) (pool : List (Ty ι)) (known : PositiveRules.Known ι) :
    Nat → Table ι → Table ι
  | 0, table => table
  | fuel+1, table =>
    let es := arrowEvidence G table pool
    let next := table.filter fun p => PositiveRules.SameKind G p.1 p.2 &&
      decide (PositiveRules.OpaqueWith G (PositiveRules.Rel table) known
        (PositiveCertificates.ArrowsChecked G table es) p.1 p.2) &&
      (sourceClauses G p.1 ++ PositiveRules.meetSources G p.1 p.2).all fun a =>
      (clausesOf G p.2).any fun b => PositiveCertificates.checkClause G table known es p.1 a b
    if next = table then table else prune G pool known fuel next

/-- Whether a core table could hold the row `(A, B)`: the conditions a row
must meet that no relation or arrow evidence decides, each source clause
covered by some target clause with every subtype and arrow premise granted.
Coverage is monotone in both, so a row failing this fails under every table:
it is left out of a table's candidates, which leaves the pruned table as it
was, and a pair failing it is refused before any table is built. Untrusted:
`checkCore` decides. -/
def rowFeasible [DecidableEq ι] (G : NormalGraph ι) (known : PositiveRules.Known ι)
    (A B : Ty ι) (schemes : Bool := false) : Bool :=
  PositiveRules.SameKind G A B &&
    decide (PositiveRules.OpaqueWith G (fun _ _ => True) known (fun _ _ _ => schemes) A B) &&
    (sourceClauses G A ++ PositiveRules.meetSources G A B).all fun a => (clausesOf G B).any fun b =>
      decide (CoversWith G (fun _ _ => True) known (fun _ _ _ => True) A a b)

/-- Known rows with the instances proving them. -/
abbrev KnownInstances (ι : Type) :=
  List (List ι × PositiveRules.Ops ι × List (RestArrow (List ι)) ×
    PositiveCertificates.Instance ι)

/-- A core table over the pool, whose coverage may use the `known` rows. -/
def subtypeWith [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι))
    (ks : KnownInstances ι) (A B : Ty ι) : Option (PositiveCertificates.Proof ι) :=
  if PositiveCertificates.checkUsing G images A B .subset then some .subset else
  -- Value top covers value types: one row, no arrow evidence.
  let toTop := PositiveCertificates.Proof.core ⟨[(A, B)], []⟩
  if expand G B = [.top] && PositiveCertificates.checkUsing G images A B toTop then some toTop else
    let known := PositiveCertificates.knownOf ks
    if !rowFeasible G known A B then none else
    let types := (A :: B :: pool).eraseDups
    let initial := (types.flatMap fun a => types.map (a, ·)).filter fun r => rowFeasible G known r.1 r.2
    let table := prune G types known initial.length initial
    let p := PositiveCertificates.Proof.core ⟨table, arrowEvidence G table types⟩ ks
    if PositiveCertificates.checkUsing G images A B p then some p else none

def subtypeBase [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι))
    (A B : Ty ι) : Option (PositiveCertificates.Proof ι) :=
  subtypeWith G images pool [] A B

/-- The pairs one signature list's coverage of another compares: each target
signature against each source one, position by position (receivers,
parameters contravariantly, results covariantly), and each part of a target
parameter's union against the source's parameter, as arrow coverage splits
it. -/
def signaturePairs (source target : List (Arrow (List ι))) :
    List (List ι × List ι) :=
  target.flatMap fun t => source.flatMap fun s =>
    (t.receiver, s.receiver) :: (s.result, t.result) :: (t.arguments.zip s.arguments).flatMap fun (q, p) =>
      (q, p) :: q.map fun l => ([l], p)

/-- The same, for variadic signatures: fixed parameters, rest and result. -/
def restPairs (source target : List (RestArrow (List ι))) :
    List (List ι × List ι) :=
  target.flatMap fun t => source.flatMap fun s =>
    (t.receiver, s.receiver) :: (t.arguments.2, s.arguments.2) :: (s.result, t.result) :: t.arguments.1.zip s.arguments.1

/-- The pairs a record's coverage of another compares, key by key: fields
both ways, views and optional fields, methods signature by signature and
scheme by scheme, and a method the source's prototype holds under the key
(its receiver against the source, its signatures against the target's
schemes'). -/
def recordPairs [DecidableEq ι] (G : NormalGraph ι) (self : List ι)
    (fs vs : List (PropKey × List ι)) (os : List (OptionalField (List ι)))
    (ms : List (MethodMembers.Sig (List ι)))
    (fs' vs' : List (PropKey × List ι)) (os' : List (OptionalField (List ι)))
    (ms' : List (MethodMembers.Sig (List ι))) : List (List ι × List ι) :=
  let slots := fs ++ vs ++ os.map fun o => (o.key, o.type)
  let keyed (k : PropKey) : List (List ι) := (slots.filter (·.1 == k)).map (·.2)
  let proto : List (List ι) := (fs ++ vs).filter (·.1 == CallArguments.protoField) |>.map (·.2)
  let schemeSigs (F : List ι) := F.filterMap G.schemes
  (fs'.flatMap fun f => (keyed f.1).flatMap fun A => [(A, f.2), (f.2, A)]) ++
  (vs'.flatMap fun f => (keyed f.1).map fun A => (A, f.2)) ++
  (os'.flatMap fun o => (keyed o.key).flatMap fun A => [(A, o.type), (o.type, A)]) ++
  ms'.flatMap fun q =>
    let own := ms.filter (·.key == q.key)
    let targetSchemes := q.schemes.flatMap schemeSigs
    (own.flatMap fun p =>
      signaturePairs (p.calls.map (·.withReceiver [])) (q.calls.map (·.withReceiver [])) ++
      (q.schemes.flatMap fun S' => p.schemes.map fun S => (S, S'))) ++
    ((keyed q.key ++ proto.flatMap fun P => (PositiveRules.viewOf G P q.key).toList).flatMap fun F =>
      (schemeSigs F).flatMap fun s =>
        (s.signatures.map fun p => (self, p.receiver)) ++
        targetSchemes.flatMap fun s' => signaturePairs s.signatures s'.signatures ++
          restPairs s.variadic s'.variadic)

/-- The pairs one clause's coverage of another compares. -/
def clausePairs [DecidableEq ι] (G : NormalGraph ι) (self : List ι) :
    Clause (List ι) → Clause (List ι) → List (List ι × List ι)
  | .refs a bs vs os ms _, .refs c ds ws ps ns _
  | .refs a bs vs os ms _, .dict c ds ws _ ps ns _ _
  | .dict a bs vs _ os ms _ _, .refs c ds ws ps ns _ =>
    recordPairs G self (a :: bs).flatten vs os ms (c :: ds).flatten ws ps ns
  | .dict a bs vs ix os ms _ cx, .dict c ds ws iy ps ns _ cy =>
    recordPairs G self (a :: bs).flatten vs os ms (c :: ds).flatten ws ps ns ++
      (iy ++ cy).flatMap fun y => (ix ++ cx).flatMap fun x => [(x.2, y.2), (y.2, x.2)]
  | .arrs L S, .arrs M T | .callable _ _ L S, .arrs M T | .callable _ _ L S, .callable _ _ M T =>
    signaturePairs L M ++ restPairs S T
  | .ctors L _, .ctors M _ =>
    signaturePairs (L.map fun p => ⟨[], p.1, p.2, .unrestricted⟩) (M.map fun p => ⟨[], p.1, p.2, .unrestricted⟩)
  | .list a bs, .list c ds | .pack a bs, .pack c ds =>
    (c :: ds).flatMap fun q => (a :: bs).flatMap fun p =>
      let pos (t : PositiveNormalization.Tuple (List ι)) := t.required ++ t.optional ++ t.rest.toList
      (pos p).flatMap fun x => (pos q).flatMap fun y => [(x, y), (y, x)]
  | _, _ => []

/-- The pairs a row's coverage compares: its clauses' against the target's,
and a scheme's signatures against a target scheme's binding the same rows. -/
def demandPairs [DecidableEq ι] (G : NormalGraph ι) (X Y : Ty ι) : List (List ι × List ι) :=
  (clausesOf G X).flatMap (fun a => (clausesOf G Y).flatMap (clausePairs G X a)) ++
  X.flatMap fun i => Y.flatMap fun j => match G.schemes i, G.schemes j with
    | some s, some s' => if s.binders = s'.binders then
        signaturePairs s.signatures s'.signatures ++ restPairs s.variadic s'.variadic else []
    | _, _ => []

/-- The most rows a table grown on demand may hold before the search gives
up on it. -/
def demandLimit : Nat := 400

/-- A core table grown from a pair on demand: each row adds the rows relating
what its coverage compares (`demandPairs`), that could hold and are not label
inclusions. A recursive family of types (`Promise<A>` and `Promise<B>`, whose
`catch` returns `Promise<A | R>` and `Promise<B | R>`) closes into a finite
table of the pairs the two unfold into together, without a table over every
type the unit names. `none` past `demandLimit` rows. Untrusted: `checkCore`
decides. -/
def demandTable [DecidableEq ι] (G : NormalGraph ι) (known : PositiveRules.Known ι) :
    Nat → Table ι → Table ι → Option (Table ι)
  | 0, _, _ => none
  | fuel + 1, table, frontier =>
    let next := (frontier.flatMap fun r => demandPairs G r.1 r.2).eraseDups.filter fun r =>
      !(r.1.all (· ∈ r.2)) && !table.contains r && rowFeasible G known r.1 r.2 true
    if next.isEmpty then some table
    else if table.length + next.length > demandLimit then none
    else demandTable G known fuel (table ++ next) next

/-- Whether a type is of objects with a member of quantified signatures: an
instance of a declaration with generic methods. -/
def quantifiedMembers (G : NormalGraph ι) (T : Ty ι) : Bool :=
  (expand G T).any fun c => match c with
    | .refs _ _ _ _ ms _ | .dict _ _ _ _ _ ms _ _ => ms.any (!·.schemes.isEmpty)
    | _ => false

/-- A proof of `A ≤ B` by a table grown on demand (`demandTable`), for two
instances of declarations with generic methods, whose unfolding together the
tables over the types near the pair do not reach. -/
def demandProof [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (A B : Ty ι) :
    Option (PositiveCertificates.Proof ι) := do
  if !(quantifiedMembers G A && quantifiedMembers G B) then none
  if !rowFeasible G [] A B true then none
  let table ← demandTable G [] demandLimit [(A, B)] [(A, B)]
  let types := (table.flatMap fun r => [r.1, r.2]).eraseDups
  let table := prune G types [] table.length table
  let p := PositiveCertificates.Proof.core ⟨table, arrowEvidence G table types⟩ []
  if PositiveCertificates.checkUsing G images A B p then some p else none


/-- The table built while matching, and the instances found for the
instantiated binders. -/
structure InstState (ι : Type) where
  table : InstTable ι := []
  found : Ctx ι := []
  /-- Meet rows of binders not yet found, matched against a clause row: the
  meet's parameters, its clauses and the row. A binder's instance is a type
  whose meet with the other parameters' instances and the clauses that row
  holds. -/
  meets : List (List ι × List (Clause (List ι)) × ι) := []

/-- Match the scheme-side type `S` against the graph's type `T` under context
`κ`, adding table entries: a parameter row to its context image, a top binder
to `T` (recorded as its instance), a row free of the context to itself, a
clause row to a clause row matched operand by operand, a meet row to the meet
row or clause row its binder's image makes it, and a scheme row to a
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
    -- Instantiation replaces operands, not effects, density, field keys or
    -- other clause structure. Check that structure before selecting an
    -- overload: matching operands alone can choose a wrong first candidate
    -- and hide a valid later signature from the independent checker.
    let clauses (st : InstState ι) (κ : Ctx ι)
        (a b : Clause (List ι)) : Option (InstState ι) :=
      if a.map (fun _ => ()) == b.map (fun _ => ()) then
        pairs st κ a.operands b.operands
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
        else if T = [p] && fixedBy G κ V p then some (add st p T)
        else match G.schemes p, T with
          | some s, [j] =>
            match G.schemes j with
            | some s2 =>
              if s2.binders.length = s.binders.length ∧
                  s2.signatures.length = s.signatures.length ∧
                  s2.variadic.length = s.variadic.length ∧
                  s2.bounds.length = s.bounds.length then
                let κ' := enter V p κ s.binders s2.binders
                -- Bounds are read outside the binders, so under `κ`.
                ((s.bounds.zip s2.bounds).foldlM (fun st pq =>
                  matchRow G bs V fuel st κ pq.1.2 pq.2.2) (add st p [j])).bind fun st =>
                ((s.signatures.zip s2.signatures).foldlM (fun st pq =>
                  if pq.1.effect != pq.2.effect then none else pairs st κ' pq.1.operands pq.2.operands)
                  st).bind fun st =>
                (s.variadic.zip s2.variadic).foldlM (fun st pq =>
                  if pq.1.effect != pq.2.effect then none else pairs st κ' pq.1.operands pq.2.operands) st
              else none
            | none => none
          | none, [j] =>
            match G.meets p with
            | some (q, cs) =>
              -- A meet row: its parameters' images decide its own. Before
              -- every binder's instance is found, nothing is matched.
              let qs := q :: G.meetParams p
              let ops := cs.flatMap Clause.operands
              let fixed (st : InstState ι) : Option (InstState ι) :=
                ops.foldlM (fun st S => matchRow G bs V fuel st κ S S) st
              let image (q : ι) := (κ.lookup q).orElse fun _ => if bs.contains q then none else some [q]
              match qs.mapM image, G.meets j with
              | none, none => some { st with meets := (qs, cs, j) :: st.meets }
              | none, _ => some st
              | some Us, some (r, ds) =>
                let rs := r :: G.meetParams j
                if Us.all (fun U => rs.any (U == [·])) ∧ rs.all (fun r => Us.contains [r]) ∧
                    ds.length = cs.length then
                  (cs.zip ds).foldlM (fun st cd => clauses st κ cd.1 cd.2)
                    (add st p [j])
                else none
              | some _, none => fixed (add st p [j])
            | none =>
              if (G p).length = (G j).length then
                ((G p).zip (G j)).foldlM (fun st cd => clauses st κ cd.1 cd.2)
                  (add st p [j])
              else none
          | _, _ => none
    | _ =>
      let positional := if S.length = T.length then
          (S.zip T).foldlM (fun st xy => matchRow G bs V fuel st κ [xy.1] [xy.2]) st
        else none
      -- A union is a set of labels: its fixed labels match themselves in `T`,
      -- and its one other label takes the rest (`undefined | T` against
      -- `boolean | undefined`).
      let fixed := S.filter fun p => T.contains p && !G.params p &&
        fixedBy G κ V p
      let bySet := match S.filter (!fixed.contains ·) with
        | [p] => matchRow G bs V fuel (fixed.foldl (fun st q => add st q [q]) st) κ [p]
            (T.filter (!fixed.contains ·))
        | _ => none
      -- A union of binders and fixed rows (`T | U`): its image is theirs
      -- together. Before the binders' instances are found, nothing is matched.
      let byParts : Option (InstState ι) := do
        let (st, img, deferred) ← S.foldlM (fun (acc : InstState ι × List ι × Bool) l =>
          let (st, img, deferred) := acc
          if G.params l then
            match κ.lookup l with
            | some U => some (add st l U, img ++ U, deferred)
            | none =>
              if bs.contains l then
                match st.found.lookup l with
                | some U => some (st, img ++ U, deferred)
                | none => some (st, img, true)
              else some (add st l [l], img ++ [l], deferred)
          else if fixedBy G κ V l then some (add st l [l], img ++ [l], deferred)
          else none) (st, [], false)
        if deferred || (img.all (· ∈ T) && T.all (· ∈ img)) then some st else none
      positional.orElse fun _ => bySet.orElse fun _ => byParts

def matchSig [DecidableEq ι] (G : NormalGraph ι) (bs : List ι) (V : FreeMap ι) (fuel : Nat)
    (st : InstState ι) (κ : Ctx ι) (p q : Arrow (List ι)) :
    Option (InstState ι) := do
  if p.effect != q.effect || p.arguments.length != q.arguments.length then none
  -- A scheme receiver admitting every value admits the target's
  -- (`instSig`): it is not matched.
  let pairs := if expand G p.receiver = [.top] then (p.result :: p.arguments).zip (q.result :: q.arguments)
    else (p.receiver :: p.result :: p.arguments).zip (q.receiver :: q.result :: q.arguments)
  pairs.foldlM (fun st xy => matchRow G bs V fuel st κ xy.1 xy.2) st

def matchRest [DecidableEq ι] (G : NormalGraph ι) (bs : List ι) (V : FreeMap ι) (fuel : Nat)
    (st : InstState ι) (κ : Ctx ι) (p q : RestArrow (List ι)) :
    Option (InstState ι) := do
  if p.effect != q.effect || p.arguments.1.length != q.arguments.1.length then none
  let pairs := if expand G p.receiver = [.top] then (p.arguments.2 :: p.result :: p.arguments.1).zip (q.arguments.2 :: q.result :: q.arguments.1)
    else (p.receiver :: p.arguments.2 :: p.result :: p.arguments.1).zip (q.receiver :: q.arguments.2 :: q.result :: q.arguments.1)
  pairs.foldlM (fun st xy => matchRow G bs V fuel st κ xy.1 xy.2) st


/-- The types a proof of `A ≤ B` may relate: the two, every row they reach,
and every operand of those rows' clauses, a union such as an index contract
`A | B` included. A certificate's table relates operands of their clauses,
which these are, so a pool of the whole table adds nothing but search. -/
def reachablePool [DecidableEq ι] (G : NormalGraph ι) (A B : Ty ι) : List (Ty ι) :=
  let D := readsFrom G closureFuel (A ++ B)
  (A :: B :: D.map ([·]) ++ D.flatMap fun i => (G i).flatMap Clause.operands).eraseDups

/-- The types two steps from `A` and `B`: their clauses' operands, and those
operands' clauses' operands. A table over them relates a record to the
contracts its fields and methods name, and those to theirs, without a table
over the whole pool; label inclusion (`Rel`) relates what lies further. -/
def nearPool [DecidableEq ι] (G : NormalGraph ι) (A B : Ty ι) : List (Ty ι) :=
  let step (T : Ty ι) : List (Ty ι) := T.flatMap fun i => (G i).flatMap Clause.operands
  -- A prototype's members are the object's methods: its operands are one
  -- step away, as an own field's are.
  let proto (T : Ty ι) : List (Ty ι) := T.flatMap fun i => (G i).flatMap fun c => match c with
    | .refs a bs vs _ _ _ =>
      (((a :: bs).flatten ++ vs).filter (·.1 == CallArguments.protoField)).map (·.2)
    | _ => []
  let one := step A ++ step B ++ (proto A ++ proto B).flatMap step
  (A :: B :: one ++ one.flatMap step).eraseDups

/-- An instance of scheme row `s` whose signatures' images are the arrows
`L`, `M`: find the binders' instances, then build the table under the context
giving each binder its instance. Untrusted: `checkInstArrs` validates it. -/
def instanceForUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (fuel : Nat) (s : SchemeRow ι)
    (L : PositiveRules.Ops ι) (M : List (RestArrow (List ι)))
    (candidates : List (Ty ι) := []) :
    Option (PositiveCertificates.Instance ι) := do
  let roots := (s.signatures.flatMap Arrow.operands ++ s.variadic.flatMap RestArrow.operands ++
    L.flatMap Arrow.operands ++ M.flatMap RestArrow.operands).flatten
  let D := readsFrom G closureFuel roots
  let V := freeMapOf G D closureFuel []
  -- Each target signature matched against one of the scheme's, fixed
  -- against fixed and variadic against variadic.
  let each (κ : Ctx ι) (st : InstState ι) : Option (InstState ι) := do
    let st ← L.foldlM (fun st q =>
      s.signatures.findSome? fun p => matchSig G s.binders V fuel st κ p q) st
    M.foldlM (fun st q =>
      s.variadic.findSome? fun p => matchRest G s.binders V fuel st κ p q) st
  let first ← each [] {}
  -- A binder read only through meet rows: an instance among the candidates
  -- whose meet with the other parameters' instances and the row's clauses is
  -- the clause row it was matched to.
  let throughMeet (b : ι) : Option (Ty ι) := first.meets.findSome? fun (qs, cs, j) =>
    if !qs.contains b then none else candidates.find? fun U =>
      match qs.mapM (fun q => if q == b then some U else
          (first.found.lookup q).orElse fun _ => if s.binders.contains q then none else some [q]) with
      | some Us =>
        let Ls := Us.map (PositiveRules.clausesOf G) ++ [cs]
        Us.all G.plainTy &&
          (PositiveRules.sameClauses (G j) (PositiveRules.meetMany Ls) ||
            PositiveRules.sameClauses (G j) (PositiveRules.meetMany Ls.reverse))
      | none => false
  let θs := s.binders.map fun b => ((first.found.lookup b).orElse fun _ => throughMeet b).getD [b]
  let κ₀ := s.binders.zip θs
  -- An instance found through a meet row is named by no target row: the
  -- table's domain holds it too.
  let (D, V) := if first.meets.isEmpty then (D, V) else
    let D := readsFrom G closureFuel (roots ++ θs.flatten)
    (D, freeMapOf G D closureFuel [])
  let each (κ : Ctx ι) (st : InstState ι) : Option (InstState ι) := do
    let st ← L.foldlM (fun st q =>
      s.signatures.findSome? fun p => matchSig G s.binders V fuel st κ p q) st
    M.foldlM (fun st q =>
      s.variadic.findSome? fun p => matchRest G s.binders V fuel st κ p q) st
  let final ← each κ₀ {}
  -- Each instance within its binder's bounds: inclusion, or a core table.
  let certs ← s.bounds.mapM fun b =>
    match κ₀.lookup b.1 with
    | none => some none
    | some U =>
      if U.all (· ∈ b.2) then some none
      else match subtypeBase G images (reachablePool G U b.2) U b.2 with
        | some (.core cert _) => some (some cert)
        | _ => none
  some ⟨final.table, θs, certs, D, V⟩

/-- A scheme row below an arrow type. -/
def instProofUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (fuel : Nat) (A B : Ty ι)
    (candidates : List (Ty ι) := []) :
    Option (PositiveCertificates.Proof ι) :=
  match A, expand G B with
  | [i], [.arrs L M] =>
    match G.schemes i with
    | some s => (instanceForUsing G images fuel s L M candidates).map .inst
    | none => none
  | _, _ => none

/-- Instances of prototype members covering the method members of the pool's
types: for a source `A` whose prototype `P` holds, under a method's key, a
scheme row, the instance whose signatures are the method's with `A` as
receiver. -/
def protoInstances [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat) :
    KnownInstances ι :=
  let methods := pool.flatMap fun B => (expand G B).flatMap fun c => match c with
    | .refs _ _ _ _ ns _ | .dict _ _ _ _ _ ns _ _ => ns
    | _ => []
  pool.flatMap fun A => (expand G A).flatMap fun c => match c with
    | .refs a bs vs _ _ _ =>
      match ((a :: bs).flatten ++ vs).lookup CallArguments.protoField with
      | some P => methods.filterMap fun q =>
          match PositiveRules.viewOf G P q.key with
          | some [i] => match G.schemes i with
            | some s =>
              let L := q.calls.map (·.withReceiver A)
              let M := q.rests.map (·.withReceiver A)
              (instanceForUsing G images fuel s L M).bind fun c =>
                if PositiveCertificates.checkInstArrsUsing G images [i] L M c then some ([i], L, M, c) else none
            | none => none
          | _ => none
      | none => []
    | _ => []

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
def genProof [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat) (A B : Ty ι) :
    Option (PositiveCertificates.Proof ι) :=
  match B with
  | [j] =>
    match G.schemes j with
    | some s => do
      let U ← pool.find? fun U => expand G U == [.arrs s.signatures s.variadic]
      let p ← subtypeBase G images pool A U <|> instProofUsing G images fuel A U
      let D := readsFrom G closureFuel A
      some (.gen D (freeMapOf G D closureFuel []) U p)
    | none => none
  | _ => none

/-- A proof of `A ≤ B`: structural, by instantiating a scheme row, or by
generalizing to one. Every proposal is checked. A core table over the two
types alone, then a renaming table, are tried before one over the whole pool,
whose size the search pays for squared: a row interned twice (`string` in a
type argument and in a bound) and two lowerings of one generic instance are
related without it. Instantiating a scheme row, which applies only when `A`
is one, comes before prototype instances, which are sought for every array
of the table against every method the table names: first over the types
near the pair, then over the whole pool. -/
def subtypeUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι))
    (A B : Ty ι) : Option (PositiveCertificates.Proof ι) :=
  let fuel := 64 + pool.length
  let ok p := PositiveCertificates.checkUsing G images A B p
  let proto (P : List (Ty ι)) := match protoInstances G images ((A :: B :: P).eraseDups) fuel with
    | [] => none
    | ks => subtypeWith G images P ks A B
  -- Every label of `A` among `B`'s: the inclusion needs no search.
  (if A.all (· ∈ B) then some .subset else none) <|>
  (subtypeBase G images [] A B) <|> ((tableProof G fuel A B).filter ok) <|>
    (subtypeBase G images (nearPool G A B) A B) <|> (demandProof G images A B) <|> (subtypeBase G images pool A B) <|>
    ((instProofUsing G images fuel A B pool).filter ok) <|> proto (nearPool G A B) <|> proto pool <|>
    ((genProof G images pool fuel A B).filter ok)
/-- Proofs that the member of key `k` on `O` covers each fixed signature of
`F`: for each, a member signature of as many parameters, each claimed
parameter within the member's and the member's result within the claimed. -/
def memberProofsUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (O : Ty ι) (k : PropKey)
    (F : Ty ι) : Option (List (List (PositiveCertificates.Proof ι) × PositiveCertificates.Proof ι)) := do
  let m ← ProgramTyping.memberOf G O k
  -- At a quantified signature, the member bound to its host is the scheme.
  if expand G F = [] && m.schemes.contains F then return []
  let [.arrs L _] := expand G F | none
  L.mapM fun q => m.calls.findSome? fun c => do
    if q.arguments.length != c.arguments.length || !c.effect.covers q.effect then none
    let ps ← (q.arguments.zip c.arguments).mapM fun (D, C) => subtypeUsing G images pool D C
    let pr ← subtypeUsing G images pool c.result q.result
    pure (ps, pr)

def coerce [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι))
    (e : ProgramCertificates.Evidence ι) (A : Ty ι) : Option (ProgramCertificates.Evidence ι) := do
  if (claim e).type = A then return e
  let p ← subtypeUsing G images pool (claim e).type A
  return .node ⟨(claim e).context, (claim e).term, A⟩ (.sub p) [e]

instance [DecidableEq ι] (G : NormalGraph ι) (B : Ty ι) (tag : Tag) (q : Bool) :
    Decidable (Answers G B tag q) := by unfold Answers; infer_instance

/-- Search ordinary typing rules. Every recursive expression request decreases
search fuel, including implicit let typing. Suggestions only prioritize candidate
types; every premise is proved in the actual context, even when the suggestion
came from a different context. No execution budget is inspected. -/
def expressionWithUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι))
    (suggestions : List (Sequent ι)) :
    Nat → List (Ty ι) → Tm → Ty ι → Option (ProgramCertificates.Evidence ι)
  | 0, _, _, _ => none
  | fuel+1, Γ, t, A => Id.run do
    -- A slot no value meets makes the context unsatisfiable: splitting it
    -- leaves no case, so the sequent holds whatever the term and its type.
    -- This is a node a refinement proved unreachable (`unionVar`).
    if let some i := Γ.findIdx? List.isEmpty then
      return some (ProgramCertificates.Evidence.node ⟨Γ,t,A⟩ (.unionVar i) [])
    let leaf := fun B r => ProgramCertificates.Evidence.node ⟨Γ,t,B⟩ r []
    let leaf' := fun (i : Nat) (C : Ty ι) => ProgramCertificates.Evidence.node ⟨Γ,.var i,C⟩ .var []
    let recur := expressionWithUsing G images pool suggestions fuel
    -- A slot of the empty type holds no value: the point is unreachable, and
    -- eliminating that union leaves no premise.
    if let some i := Γ.findIdx? (·.isEmpty) then
      return some (.node ⟨Γ,t,A⟩ (.unionVar i) [])
    -- Union elimination refines an immutable receiver slot in each premise;
    -- it neither evaluates the operation twice nor inserts a runtime tag test.
    let splitReceiver := fun receiver => do
      let .var i := receiver | none
      let B ← Γ[i]?
      if B.length ≤ 1 then none else do
        let ps ← B.mapM fun b => recur (Γ.set i [b]) t A
        pure (ProgramCertificates.Evidence.node ⟨Γ,t,A⟩ (.unionVar i) ps)
    -- The types an operand may be read at as a string: a slot's own, then
    -- the pool's, each all strings.
    let stringOperands := fun (a : Tm) =>
      ((match a with | .var i => (Γ[i]?).toList | _ => []) ++ pool).filter fun S =>
        decide (Answers G S .isStr true)
    match t with
    | .var i => return (Γ[i]?).bind fun B => coerce G images pool (leaf B .var) A
    | .nul | .undef | .tru | .fls =>
      let r := match t with | .nul => Rule.nul | .undef => .undef | .tru => .tru | _ => .fls
      return (A :: pool).findSome? fun B =>
        let r := if expand G B = [.boolLit true] && t == .tru then Rule.truLit
          else if expand G B = [.boolLit false] && t == .fls then Rule.flsLit else r
        if checkTreeUsing G images (leaf B r) then coerce G images pool (leaf B r) A else none
    -- A number has one rule: its own singleton. Reaching `number`, or any
    -- union above it, is the coercion's job, exactly as for a boolean literal.
    | .num _ =>
      -- Its own singleton where the claim names one, the family where it does
      -- not: a literal claimed at `number` has no singleton label to coerce
      -- from, exactly as a Boolean claimed at `boolean` has none.
      return (A :: pool).findSome? fun B =>
        if checkTreeUsing G images (leaf B .numLit) then coerce G images pool (leaf B .numLit) A
        else if checkTreeUsing G images (leaf B .num) then coerce G images pool (leaf B .num) A
        else none
    | .str _ =>
      return (A :: pool).findSome? fun B =>
        if checkTreeUsing G images (leaf B .strLit) then coerce G images pool (leaf B .strLit) A
        else if checkTreeUsing G images (leaf B .str) then coerce G images pool (leaf B .str) A
        else none
    | .bigint _ =>
      return (A :: pool).findSome? fun B =>
        if checkTreeUsing G images (leaf B .bigintLit) then coerce G images pool (leaf B .bigintLit) A
        else if checkTreeUsing G images (leaf B .bigint) then coerce G images pool (leaf B .bigint) A
        else none
    -- Graph code: its captures at their slots' types, the code the unit's
    -- table checked; the claim or a pool type. A function's (`Rule.funGraph`)
    -- has a fresh bag; with a rest, each variadic signature's store is at a
    -- pool type that is its rest store. A class value's (`Rule.ctorGraph`)
    -- has its receiver slot at a pool type that is exactly `undefined`, what
    -- `new` passes there. A callable object's (`Rule.callableGraph`) has the
    -- bag's initializers, then the captures.
    | .makeAt (.graph _ _ _ _ caps kind rest) ns inits =>
      let some slots := ProgramCertificates.varSlots caps | return none
      let some ps := slots.mapM (fun i => (Γ[i]?).map fun C => leaf' i C) | return none
      let arraysOf := fun (S : List (RestArrow (Ty ι))) =>
        if rest then S.mapM fun p => pool.find? fun R => decide (RestStore G R p.arguments.2) else some []
      let fresh := ns == [valueField] && inits == [.nul]
      return (A :: pool).findSome? fun F => do
        match kind, expand G F with
        | .call, [.arrs _ S] =>
          if !fresh then none else do
          coerce G images pool (.node ⟨Γ,t,F⟩ (.funGraph (← arraysOf S)) ps) A
        | .construct, [.ctors _] =>
          if !fresh then none else do
          let U ← pool.find? fun U => decide (expand G U = [.undef])
          coerce G images pool (.node ⟨Γ,t,F⟩ (.ctorGraph U) ps) A
        | .call, [.callable P [] _ S] =>
          if P.map Prod.fst != ns || inits.length != ns.length then none else do
          let eas ← (inits.zip (P.map Prod.snd)).mapM fun (a,D) => recur Γ a D
          coerce G images pool (.node ⟨Γ,t,F⟩ (.callableGraph (← arraysOf S)) (eas ++ ps)) A
        | _, _ => none
    -- `new f(args)`: a construct signature of the constructor's type taking at
    -- least as many parameters as there are actuals; each omitted position
    -- proves `undefined`, as a call's does.
    | .construct f args =>
      return pool.findSome? fun F => do
        let [.ctors L] := expand G F | none
        L.findSome? fun p => do
          if args.length > p.1.length then none else do
          let _ ← subtypeUsing G images pool p.2 A
          let ef ← recur Γ f F
          let eas ← (args.zip p.1).mapM fun (a,D) => recur Γ a D
          let eus ← (p.1.drop args.length).mapM fun D => recur Γ .undef D
          coerce G images pool (.node ⟨Γ,t,p.2⟩ .construct (ef :: eas ++ eus)) A
    -- `.bind`'s forwarding descriptor: a leaf whose checker reads the saved
    -- slots from the context; the claimed type, or a pool type, is its result.
    | .makeAt (.bound (.var _) (.var _) _) [] [] =>
      return (A :: pool).findSome? fun F =>
        if checkTreeUsing G images (leaf F .bindE) then coerce G images pool (leaf F .bindE) A
        else if checkTreeUsing G images (leaf F .bindRestE) then coerce G images pool (leaf F .bindRestE) A
        else none
    -- A member bound to its host: a leaf whose checker reads the object's type
    -- from the context; the claimed type, or a pool type, is its result.
    | .letE (.readAt k (.var i)) (.makeAt (.bound (.var 0) (.var _) []) [] []) =>
      let schemes := match Γ[i]? with
        | some O => ProgramTyping.memberSchemes G O k
        | none => []
      return (A :: schemes ++ pool).findSome? fun F => do
        let ps ← memberProofsUsing G images pool (← Γ[i]?) k F
        if checkTreeUsing G images (leaf F (.bindMember ps)) then coerce G images pool (leaf F (.bindMember ps)) A
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
      -- A callee read from a slot is tried first at the slot's own type, a
      -- fixed signature before any variadic one of the pool: coercing it to
      -- each of those first, where its own type is fixed, fails at the cost
      -- of a table over the pool each time. Order only; every premise is
      -- still proved.
      let own := match f with | .var i => (Γ[i]?).toList | _ => []
      -- A variadic callee: the receiver at the signature's receiver, the fixed
      -- actuals at its parameters, then the further parts: with a spread, each
      -- at the element rest's element, or a spread of a pool store type whose
      -- elements are; without one, each at its position in the rest's tuple.
      let variadic := fun (candidates : List (Ty ι)) => candidates.findSome? fun F => do
        (restSigs G F).findSome? fun ⟨Rt, (Ps, P), B, effect⟩ => do
          -- Fixed actuals first; a shorter call omits trailing fixed positions,
          -- each proving `undefined`, and writes no further part.
          let k := min args.length Ps.length
          let omitted := Ps.drop k
          let parts := args.drop k
          if !omitted.isEmpty && !parts.isEmpty then none else do
          let _ ← subtypeUsing G images pool B A
          let ef ← recur Γ f F
          let er ← recur Γ recv Rt
          let eas ← (args.zip Ps).mapM fun (a,D) => recur Γ a D
          let eus ← omitted.mapM fun D => recur Γ .undef D
          let flags := parts.map fun a => match a with | .spread _ => true | _ => false
          let eps ← if flags.any id then do
              let E ← restElem G P
              parts.mapM fun a => match a with
                | .spread s => pool.findSome? fun S =>
                    if decide (SpreadsInto G S E) then recur Γ s S else none
                | a => recur Γ a E
            else do
              let [.pack T []] := expand G P | none
              parts.zipIdx.mapM fun (a, i) => do recur Γ a (← positionTy T i)
          let e := ProgramCertificates.Evidence.node ⟨Γ,t,B⟩
            (.callRest effect k omitted.length flags P) (ef :: er :: eas ++ eus ++ eps)
          if checkTreeUsing G images e then coerce G images pool e A else none
      let direct := fun (candidates : List (Ty ι)) => candidates.findSome? fun F => do
        let (L,r) ← match expand G F with
          | [.arrs L _] => some (L,Rule.app)
          | [.callable _ _ L _] => some (L,Rule.callCallable)
          | _ => none
        L.findSome? fun p => do
          -- Require every operand before searching the premises. A signature
          -- with more positions than the call writes is usable when each
          -- remaining contract admits `undefined`, the value bound there.
          if args.length > p.arguments.length then none else do
            let omitted := p.arguments.drop args.length
            let _ ← subtypeUsing G images pool p.result A
            let ef ← recur Γ f F
            let er ← recur Γ recv p.receiver
            let eas ← (args.zip p.arguments).mapM fun (a,D) => recur Γ a D
            let eus ← omitted.mapM fun D => recur Γ .undef D
            coerce G images pool (.node ⟨Γ,t,p.result⟩ (r p.effect) (ef :: er :: eas ++ eus)) A
      if let some e := variadic own <|> direct own <|> variadic pool <|> direct pool then return some e
      -- A callee or, for a method dispatched on its object, the receiver.
      return splitReceiver f <|> splitReceiver recv
    | .makeAt .absent ns inits =>
      return (A :: pool).findSome? fun R => do
        if !(decide ns.Nodup) then none else do
        if inits.length != ns.length then none else do
        match expand G R with
        | [.refs B [] [] [] [] ks] =>
          if B.map Prod.fst != ns || !ks.all (fun K => ns.all K.admits) then none else do
          let ps ← (inits.zip (B.map Prod.snd)).mapM fun (a,D) => recur Γ a D
          coerce G images pool (.node ⟨Γ,t,R⟩ .alloc ps) A
        -- A literal allocated directly at a dictionary, each field an index
        -- may admit at that index's type.
        | [.dict B [] [] ix os [] [] cs] =>
          if B.map Prod.fst != ns || ns.contains CallArguments.protoField ||
            !B.all (fun f => (ix ++ cs).all fun y => !y.1.may f.1 || f.2 == y.2) ||
            !os.all (fun o => !ns.contains o.key && cs.all fun y => !y.1.may o.key ||
              o.type == y.2 || (G.plainTy y.2 && (expand G y.2).isEmpty)) then none else do
          let ps ← (inits.zip (B.map Prod.snd)).mapM fun (a,D) => recur Γ a D
          coerce G images pool (.node ⟨Γ,t,R⟩ .alloc ps) A
        | _ => none
    | .indexAt a key =>
      -- A key of a class within an index's reads through it: a string
      -- through a string index, a number through a number or string index, a
      -- symbol through a symbol index.
      return (A :: pool).findSome? fun R => do
        let [.dict _ [] _ ix _ _ _ _] := expand G R | none
        ix.findSome? fun (Kx, E) =>
        [IndexKeys.strings, .numeric, .symbols].findSome? fun KK => do
          if !KK.within Kx then none else do
          (A :: pool).findSome? fun K => do
            if expand G K != [keyClause KK] then none else do
            (A :: pool).findSome? fun U => do
              if expand G U != [.undef] then none else do
              let B := E ++ U
              let _ ← subtypeUsing G images pool B A
              let ea ← recur Γ a R
              let ek ← recur Γ key K
              coerce G images pool (.node ⟨Γ,t,B⟩ (.indexDict Kx KK E U) [ea, ek]) A
    | .readAt f a =>
      let direct := pool.findSome? fun R => do
        -- An invariant field reads at its contract; a view field at its bound;
        -- an optional field, writable or readonly, at its type or `undefined`; a key a
        -- bound does not admit at the prototype's field or view.
        let (B,r) ← match expand G R with
          | [.refs fs [] vs os _ ks] =>
            (fs.lookup f).map (·,Rule.read) <|> (vs.lookup f).map (·,Rule.readView) <|>
              (((os.find? (·.key == f)).map (·.type)).bind fun E => pool.findSome? fun U =>
                if expand G U == [.undef] then some (E ++ U, Rule.readOptional E U) else none) <|>
              (if ks.any (fun K => !K.admits f) then
                ((fs ++ vs).lookup CallArguments.protoField).bind fun P =>
                  match expand G P with
                  | [.refs gs [] ws _ _ _] => ((gs ++ ws).lookup f).map (·, Rule.readProto P)
                  | _ => none
              else none)
          | [.callable fs _ _ _] => (fs.lookup f).map (·,Rule.readCallable)
          -- A dictionary's named field or view, else its index, which may miss.
          -- The index holds of every present field, an optional one included.
          | [.dict fs [] vs ix _ _ _ _] =>
            (fs.lookup f).map (·,Rule.read) <|> (vs.lookup f).map (·,Rule.readView) <|>
            (numericFirst ix).findSome? fun (K, B) => if !K.surely f then none else
              pool.findSome? fun U =>
                if expand G U == [.undef] then some (B ++ U, Rule.readDict K B U) else none
          | _ => none
        let _ ← subtypeUsing G images pool B A
        let ea ← recur Γ a R
        coerce G images pool (.node ⟨Γ,t,B⟩ r [ea]) A
      if let some e := direct then return some e
      return splitReceiver a
    | .writeAt f a b =>
      let direct := pool.findSome? fun R => do
        let (fs,r) ← match expand G R with
          | [.refs fs [] _ _ _ _] => some (fs,Rule.write)
          | [.callable fs _ _ _] => some (fs,Rule.writeCallable)
          | _ => none
        let B ← fs.lookup f
        let ea ← recur Γ a R
        let eb ← recur Γ b B
        (A :: pool).findSome? fun N =>
          let e := ProgramCertificates.Evidence.node ⟨Γ,t,N⟩ r [ea,eb]
          if checkTreeUsing G images e then coerce G images pool e A else none
      if let some e := direct then return some e
      return splitReceiver a
    | .arith op a b =>
      -- Each operand at a pool type of the operand clauses the operator
      -- takes (numbers and bigints; strings too for a comparison, every
      -- printable primitive for `+`, and any for `===`), the right one only where the pair
      -- classifies; the rule then checks every pair and the result, at the
      -- requested type when it holds the result's kind, else coerced.
      let operands := pool.filter fun R => G.plainTy R && !(expand G R).isEmpty &&
        (expand G R).all fun c => numberClause c || bigintClause c || (op.relational && stringClause c)
          || (op == .add && printableClause c) || op == .eq
      return operands.findSome? fun R => do
        let ea ← recur Γ a R
        (operands.filter fun S => (operandsResult G op R S).isSome).findSome? fun S => do
          let eb ← recur Γ b S
          (A :: pool).findSome? fun N =>
            let e := ProgramCertificates.Evidence.node ⟨Γ,t,N⟩ .arith [ea,eb]
            if checkTreeUsing G images e then coerce G images pool e A else none
    -- A copy of a spread: a store type of any length at some element type,
    -- and a pool store type whose elements it admits.
    | .arrLit [.spread src] =>
      return (A :: pool).findSome? fun L => do
        let [.list ⟨[], [], some E, false, _⟩ []] := expand G L | none
        pool.findSome? fun S => do
          if !decide (SpreadsInto G S E) then none else do
          let es ← recur Γ src S
          coerce G images pool (.node ⟨Γ,t,L⟩ (.arrCopy E) [es]) A
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
        if checkTreeUsing G images e then coerce G images pool e A else none
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
            | some B => coerce G images pool (.node ⟨Γ,t,B⟩ .elem [ea,ei]) A
            | none => do
              let B ← positionTy T k
              (A :: pool).findSome? fun U =>
                let e := ProgramCertificates.Evidence.node ⟨Γ,t,B ++ U⟩ (.elemOpt U) [ea,ei]
                if checkTreeUsing G images e then coerce G images pool e A else none
          | _ =>
            match T with
            | ⟨[], [], some E, _, _⟩ =>
              (A :: pool).findSome? fun U =>
                let e := ProgramCertificates.Evidence.node ⟨Γ,t,E ++ U⟩ (.elemAny U) [ea,ei]
                if checkTreeUsing G images e then coerce G images pool e A else none
            | _ => none
      if let some e := direct then return some e
      -- A string's code unit at a numeric key: a string or `undefined`.
      let string := (stringOperands a).findSome? fun S => do
        let ea ← recur Γ a S
        pool.findSome? fun I => do
          if !decide (Answers G I .isNum true) then none else do
          let ei ← recur Γ i I
          (A :: pool).findSome? fun T => do
            if expand G T != [.str] then none else do
            (A :: pool).findSome? fun U =>
              if expand G U != [.undef] then none else
              coerce G images pool (.node ⟨Γ,t,T ++ U⟩ (.elemStr T U) [ea,ei]) A
      if let some e := string then return some e
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
          if checkTreeUsing G images e then coerce G images pool e A else none
    | .lenOf a =>
      let store := pool.findSome? fun L => do
        let [.list _ []] := expand G L | none
        let ea ← recur Γ a L
        (A :: pool).findSome? fun N =>
          let e := ProgramCertificates.Evidence.node ⟨Γ,t,N⟩ .len [ea]
          if checkTreeUsing G images e then coerce G images pool e A else none
      -- A string's own `length`.
      return store <|> (stringOperands a).findSome? fun S => do
        let ea ← recur Γ a S
        (A :: pool).findSome? fun N =>
          let e := ProgramCertificates.Evidence.node ⟨Γ,t,N⟩ .lenStr [ea]
          if checkTreeUsing G images e then coerce G images pool e A else none
    | .merge d a b =>
      -- The accumulator and the source at their slots' types, or a pool
      -- type; the result the requested type, when every pair of their
      -- clauses merges into it, else a pool type coerced to it.
      let slot (x : Tm) := match x with | .var i => Γ[i]?.toList | _ => []
      return (slot a ++ pool).findSome? fun R => do
        let ea ← recur Γ a R
        (slot b ++ pool).findSome? fun S => do
          let eb ← recur Γ b S
          (A :: pool).findSome? fun N =>
            if ObjectMerge.MergeOk G d R S N then
              coerce G images pool (.node ⟨Γ,t,N⟩ .merge [ea,eb]) A
            else none
    | .throw a =>
      -- A throw has every type; its operand, at a type of its own.
      let types := (match a with | .var i => Γ[i]?.toList | _ => []) ++ pool
      return types.findSome? fun B => do
        let ea ← recur Γ a B
        some (ProgramCertificates.Evidence.node ⟨Γ,t,A⟩ .throw [ea])
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
def expressionUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) :=
  expressionWithUsing G images pool []

/-- Gather graph labels, every operand of their clauses and supplied union
types. Hints may add intermediate types; they cannot change claims or bypass
evidence checking. -/
def vocabulary [DecidableEq ι] (G : NormalGraph ι) (labels : List ι)
    (claims : List (PointClaim ι)) (hints : List (Ty ι)) : List (Ty ι) :=
  ([] :: (labels.map fun i => [i]) ++ hints ++
    claims.flatMap (fun c => c.type :: c.context) ++
    labels.flatMap (fun i => (G i).flatMap Clause.operands)).eraseDups

inductive Failure where
  | claimCount
  | expression (label : Nat)
  | edge (source : Nat) (destination : Nat) (edgeIndex : Nat)
  | rejected
  deriving DecidableEq, Repr

/-- Ordinary and observed edges share slot selection and coverage search. The
observation comes from graph dispatch, never from supplied point annotations. -/
def edgeUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι))
    (claims : List (PointClaim ι)) (Γ : List (Ty ι)) (target : Target)
    (observed : Option (Nat × BranchRefinement.Observation) := none)
    (fields : List (Nat × PropKey) := []) (optionals : List (Nat × PropKey) := []) :
    Option (EdgeEvidence ι) := do
  let c ← claims[target.label]?
  if let some (tested, o) := observed then
    if Γ[tested]?.isNone then failure
    -- An observation the tested type rules out: the edge is never taken.
    if (Γ[tested]?).any (BranchRefinement.impossible G · o) then
      return List.replicate c.context.length .subset
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
        | .tag t q =>
          if BranchRefinement.tagMember G B t q then pure .subset
          else (subtypeUsing G images pool (BranchRefinement.tagSlice G A t q) B).orElse fun _ =>
            -- A passed `in` test: the key is present from then on.
            if BranchRefinement.presentKey t q (BranchRefinement.promotes G (BranchRefinement.tagSlice G A t q) B)
            then some .subset
            -- A passed `Array.isArray`: a record's member is an array of the realm.
            else if t == .isArray && q && BranchRefinement.arraySlice G A B then some .subset
            else none
      else (subtypeUsing G images pool A B).orElse (fun _ => match o with
        -- An object the tested value was read from keeps the labels whose
        -- field admits the observation.
        | .tag t q => (fields ++ optionals).findSome? fun (k, f) =>
            if k == slot target.mapping i then subtypeUsing G images pool (BranchRefinement.fieldSlice G A f t q) B
            else none
        | .boolean _ => none) |>.orElse fun _ =>
        -- One read through an optional key, where the observation rules out
        -- the `undefined` an absent key reads: the key is present.
        if BranchRefinement.excludesUndef o && optionals.any (fun (k, f) =>
            k == slot target.mapping i && BranchRefinement.promotes G A B f)
        then some .subset else none
    | none => subtypeUsing G images pool A B


/-- Select effect evidence without changing the requested sequent. A precise
read/value rule may succeed when ordinary derivation search cannot. -/
def expressionEffectUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι))
    (fuel : Nat) (j : Sequent ι) (k : HeapKnowledge.Knowledge)
    (suggestions : List (Sequent ι)) (known : List (Evidence ι))
    (codes : CodeEntry ι → Bool := fun _ => false) :
    Option (Evidence ι × HeapExpressionRules.StepEvidence ι × HeapKnowledge.Knowledge) := Id.run do
  -- A node's derivation is first sought among its own types: its claim and
  -- its context's, which are its operands' claims. The pool is consulted
  -- only where those leave a choice open.
  let own := (j.type :: j.context).eraseDups
  let ordinary := (known.find? fun e => claim e == j).orElse fun _ =>
    (expressionWithUsing G images own suggestions fuel j.context j.term j.type).orElse fun _ =>
      expressionWithUsing G images pool suggestions fuel j.context j.term j.type
  let mut choices : List (HeapExpressionRules.StepEvidence ι) := []
  match j.term with
  | .var i =>
    if let some R := HeapExpressionRules.valuesAt G j.context k i then
      choices := [.knownValue i R]
  | .readAt fld (.var i) =>
    choices := (k.cells.filter fun f => f.slot == i && f.field == fld).map
      fun f => .observedRead i f.contents
    -- A location a fact says holds no `undefined`: the read at its
    -- contract, sliced, below the claim.
    if let some Ref := j.context[i]? then
      if HeapExpressionRules.fieldOperand (expand G Ref) fld &&
          k.cells.any (fun f => f.slot == i && f.field == fld && f.contents.all (· != .undef)) then
        if let [.refs fs _ _ _ _ _] := expand G Ref then
          if let some C := fs.lookup fld then
            if let some e := expressionWithUsing G images (C :: own) suggestions fuel j.context j.term C then
              if let some p := subtypeUsing G images pool (BranchRefinement.tagSlice G C .isUndef false) j.type then
                choices := choices ++ [.slicedRead i e p]
  | _ => pure ()
  if let some e := ordinary then
    match j.term with
    | .readAt fld (.var i) =>
      if let some Ref := j.context[i]? then
        if HeapExpressionRules.fieldOperand (expand G Ref) fld ||
            HeapExpressionRules.optionalOperand (expand G Ref) fld then
          choices := choices ++ [.typedRead i e]
    | .makeAt .. | .merge .. | .arrLit .. =>
      choices := choices ++ [.allocated e]
    | .writeAt _ (.var i) (.var v) =>
      choices := choices ++ [.written i v (HeapExpressionRules.valuesAt G j.context k v) e]
    | _ => pure ()
    choices := choices ++ [.created e,.pure e,.ordinary e]
  for effect in choices do
    if let some out := HeapExpressionRules.checkStepUsing G images j k effect codes then
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

private def produceNode [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι))
    (fuel l : Nat) (node : Node) (claims : List (PointClaim ι))
    (k : HeapKnowledge.Knowledge) (suggestions : List (Sequent ι)) (known : List (Evidence ι))
    (codes : CodeEntry ι → Bool := fun _ => false) :
    Except Failure (NodeEvidence ι) := do
  let some c := claims[l]? | throw .claimCount
  let some (e,effect,out) :=
    expressionEffectUsing G images pool fuel ⟨c.context,node.expression,c.type⟩ k suggestions known codes
    | throw (.expression l)
  let target := fun Γ t index => match edgeUsing G images pool claims Γ t with
    | some p => Except.ok p
    | none => Except.error (Failure.edge l t.label index)
  let branchTarget := fun Γ o t index => match edgeUsing G images pool claims Γ t (some (0, o)) (readFields out 0)
      (optionalFields out 0) with
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
  -- A handler receives the thrown value at a type admitting every value: the
  -- type its target states for the slot it lands in, else one from the pool.
  let hd ← (match node.handler with
    | none => pure none
    | some t =>
      let landing := ((claims[t.label]?).toList.flatMap fun tc =>
        (List.range tc.context.length).filterMap fun i =>
          if PointClaims.slot t.mapping i == 0 then tc.context[i]? else none)
      match (landing ++ pool).findSome? fun T =>
          if ControlFlow.admitsAll G T then (edgeUsing G images pool claims (T :: c.context) t).map (T, ·) else none with
      | some x => pure (some x)
      | none => throw (Failure.edge l t.label (successors node.continuation).length)
    : Except Failure (Option (Ty ι × EdgeEvidence ι)))
  return {expression := e, edges := ps, knowledge := k, effect := some effect, output := out, handler := hd}

/-- Propagate established postconditions along single-predecessor paths. Entry
starts empty; source cuts use exactly their supplied requirements, even when
empty. Other merge points use supplied requirements. A node is checked once
when its unique predecessor is available; this is dependency scheduling, not invariant iteration.
Every edge is still checked by the independent consumer. -/
def produceRawUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι))
    (fuel : Nat) (P : Program) (claims : List (PointClaim ι))
    (suggestions : List (Sequent ι) := []) (known : List (Evidence ι) := []) (start : Nat := 0)
    (requirements : List (Nat × HeapKnowledge.Knowledge) := []) (cuts : List Nat := [])
    (codes : CodeEntry ι → Bool := fun _ => false) :
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
      let evidence ← produceNode G images pool fuel l node claims k suggestions known codes
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

def produceUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (labels : List ι)
    (fuel : Nat) (R : Ty ι) (P : Program) (claims : List (PointClaim ι))
    (start : Nat) (hints : List (Ty ι) := []) (inputs : List (Ty ι) := [])
    (suggestions : List (Sequent ι) := []) (known : List (ProgramCertificates.Evidence ι) := [])
    (requirements : List (Nat × HeapKnowledge.Knowledge) := []) (cuts : List Nat := [])
    (codes : CodeEntry ι → Bool := fun _ => false) : Except Failure (ControlFlow.Certificate ι) :=
  match produceRawUsing G images (vocabulary G labels claims (inputs ++ hints)) fuel P claims suggestions known start requirements cuts codes with
  | .error e => .error e
  | .ok C => if acceptUsing G images R P claims C start inputs codes then .ok C
    else .error ((failedEdge P C).getD .rejected)

theorem produce_checked [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {labels fuel R P claims start hints inputs suggestions known requirements cuts codes C}
    (h : produceUsing G images labels fuel R P claims start hints inputs suggestions known requirements cuts codes = .ok C) :
    acceptUsing G images R P claims C start inputs codes = true := by
  unfold produceUsing at h
  split at h
  · contradiction
  · split at h
    · cases h; assumption
    · contradiction

/-! Search proposes, and acceptance decides, with one proved instance image
checker. The finite one is the default of the existing entry points. -/
abbrev accept [DecidableEq ι] (G : NormalGraph ι) := @acceptUsing _ _ G (finiteInstanceImages G)
abbrev instanceFor [DecidableEq ι] (G : NormalGraph ι) := @instanceForUsing _ _ G (finiteInstanceImages G)
abbrev instProof [DecidableEq ι] (G : NormalGraph ι) := @instProofUsing _ _ G (finiteInstanceImages G)
abbrev subtype [DecidableEq ι] (G : NormalGraph ι) := @subtypeUsing _ _ G (finiteInstanceImages G)
abbrev memberProofs [DecidableEq ι] (G : NormalGraph ι) := @memberProofsUsing _ _ G (finiteInstanceImages G)
abbrev expressionWith [DecidableEq ι] (G : NormalGraph ι) :=
  @expressionWithUsing _ _ G (finiteInstanceImages G)
abbrev expression [DecidableEq ι] (G : NormalGraph ι) := @expressionUsing _ _ G (finiteInstanceImages G)
abbrev edge [DecidableEq ι] (G : NormalGraph ι) := @edgeUsing _ _ G (finiteInstanceImages G)
abbrev expressionEffect [DecidableEq ι] (G : NormalGraph ι) :=
  @expressionEffectUsing _ _ G (finiteInstanceImages G)
abbrev produceRaw [DecidableEq ι] (G : NormalGraph ι) := @produceRawUsing _ _ G (finiteInstanceImages G)
abbrev produce [DecidableEq ι] (G : NormalGraph ι) := @produceUsing _ _ G (finiteInstanceImages G)

#print axioms accepted_from_inputs
#print axioms accepted_safe
#print axioms produce_checked
end Verification.Model.CertificateProducer
