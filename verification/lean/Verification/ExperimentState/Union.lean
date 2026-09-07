import Verification.ExperimentState.Rules
/-!
# Unions in operand position

`Completeness.lean` settles equality for regular types whose constructors take a
single operand. Real types put unions *inside* constructors — `{ next: A | B }`,
`A → (B | C)` — and that cannot be normalised away, since `ref A ∨ ref B` is not
`ref (A ∨ B)`. So the representation has to carry unions in operand position from
the start, which is what this file does: a node's operands are *sets* of nodes,
read as their union, and a type is likewise a set of nodes.

Guardedness is unchanged. Every operand still sits beneath a `ref` or an `arr`,
both of which read below the current budget, so the fixed point exists for the
same reason as before and the tower argument is untouched.

## Why clause-to-clause covering is the right shape here

The classical obstacle to matching each source clause against a *single* target
clause is splitting. In a pure model

    nul → (nul ∨ bool)  ≤  (nul → nul) ∨ (nul → bool)

holds — a function on a one-element domain either returns a null or returns a
boolean — and no clause-to-clause rule can derive it.

`no_arrow_splitting` shows that inclusion is **false** here. The language has no
conditional, but a mutable cell is a branch: a reader of a cell declared
`nul ∨ bool` lies in the source type and in neither disjunct, because an arrow
quantifies over every satisfying heap, and one heap holds `true` where another
holds `null`. State supplies the observation a typecase would have.

That is why covering *is* complete over this representation, which is the
opposite of what semantic subtyping predicts for a pure language. `sim_iff_incl`
is the statement: for a well-formed graph, one type is included in another
exactly when a covering certificate says so.
-/

namespace Verification
namespace ExperimentState
namespace Union

/-! ## Splitting fails, which is what leaves room for single-clause matching -/

/-- `nul ∨ bool`. -/
def uT : Fam := unionT nulT boolT

theorem uT_adm : Adm uT := unionT_adm nulT boolT nulT_adm boolT_adm

theorem uT_valOnly : ValOnly uT := by
  intro _ _ a ha
  rcases (ha : nulT _ _ a ∨ boolT _ _ a) with h | h
  · cases (h : a = .nul); rfl
  · rcases (h : a = .tru ∨ a = .fls) with rfl | rfl <;> rfl

/-- One cell, declared `nul ∨ bool`, and a function that reads it. -/
def Wu (k : Nat) : WorldT k := ofList [res uT]
def readCell : Tm := .lam (.read (.loc 0))

theorem Wu_lookup (k : Nat) : lookup (Wu k) 0 = some (res uT) := by simp [lookup, Wu]

theorem Wu_trunc {k j : Nat} (h : j ≤ k) : trunc j h (Wu k) = Wu j := by
  simp only [Wu, trunc, toList_ofList, List.map_cons, List.map_nil]; rfl

theorem Wu_adm (k : Nat) : WorldAdm (Wu k) := by
  intro l c hl
  simp only [lookup, Wu, toList_ofList] at hl
  cases l with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hl
    subst hl
    exact fun j _ U U' hx v hv => uT_adm.mono j U U' hx v hv
  | succ k => simp at hl

theorem Wu_heap (n : Nat) (v : Val) (hv : uT n (Wu n) v) : HeapOk n (Wu n) [v] := by
  refine ⟨by simp [Wu], ?_⟩
  intro l c hl
  simp only [lookup, Wu, toList_ofList] at hl
  cases l with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hl
    subst hl
    refine ⟨v, rfl, fun j hj => ?_⟩
    show uT j _ v
    rw [Wu_trunc]
    exact uT_adm.down_le n j (by omega) (Wu n) v hv
  | succ k => simp at hl

theorem read_in_union (k : Nat) : arrowT nulT uT k (Wu k) readCell := by
  refine lam_intro nulT_valOnly _ k (Wu k) ?_
  intro p _ W' hW hadm hh hok a _
  rw [Wu_trunc] at hW
  have hl0 : lookup W' 0 = some (res uT) := WExt_lookup hW (Wu_lookup _)
  show Safe uT p _ hh (.read (.loc 0))
  exact read_rule uT_valOnly p _ hh 0 (WorldAdm_trunc _ hadm) (HeapOk_trunc p W' hh hok)
    (lookup_trunc (Nat.le_succ p) W' 0 (res uT) hl0) (fun _ _ _ _ => Iff.rfl)

theorem read_not_in_nul : ¬ arrowT nulT nulT 5 (Wu 5) readCell := by
  intro hb
  have h4 := hb.2 4 (by omega) (Wu 4) (by rw [Wu_trunc]; exact WExt_refl _) (Wu_adm 4)
    [.tru] (Wu_heap 4 .tru (Or.inr (Or.inl rfl))) .nul rfl
  rcases h4 with ⟨hv, -⟩ | ⟨W1, h1, t1, -, -, hs1, -, hsafe1⟩
  · simp [isVal] at hv
  · cases hs1 with
    | appL hs => exact lam_no_step hs
    | appR _ hs => exact nul_no_step hs
    | beta _ =>
      rcases hsafe1 with ⟨hv, -⟩ | ⟨W2, h2, t2, -, -, hs2, -, hsafe2⟩
      · simp [subst, isVal] at hv
      · cases hs2 with
        | readC hs => exact loc_no_step hs
        | readV hval =>
          simp at hval
          subst hval
          rcases hsafe2 with ⟨-, hn⟩ | ⟨W3, h3, t3, -, -, hs3, -, -⟩
          · simp [nulT] at hn
          · exact tru_no_step hs3

theorem read_not_in_bool : ¬ arrowT nulT boolT 5 (Wu 5) readCell := by
  intro hb
  have h4 := hb.2 4 (by omega) (Wu 4) (by rw [Wu_trunc]; exact WExt_refl _) (Wu_adm 4)
    [.nul] (Wu_heap 4 .nul (Or.inl rfl)) .nul rfl
  rcases h4 with ⟨hv, -⟩ | ⟨W1, h1, t1, -, -, hs1, -, hsafe1⟩
  · simp [isVal] at hv
  · cases hs1 with
    | appL hs => exact lam_no_step hs
    | appR _ hs => exact nul_no_step hs
    | beta _ =>
      rcases hsafe1 with ⟨hv, -⟩ | ⟨W2, h2, t2, -, -, hs2, -, hsafe2⟩
      · simp [subst, isVal] at hv
      · cases hs2 with
        | readC hs => exact loc_no_step hs
        | readV hval =>
          simp at hval
          subst hval
          rcases hsafe2 with ⟨-, hn⟩ | ⟨W3, h3, t3, -, -, hs3, -, -⟩
          · simp [boolT] at hn
          · exact nul_no_step hs3

/-- **Arrows do not split over unions here.** The inclusion that defeats
clause-to-clause covering in a pure model fails in this one. -/
theorem no_arrow_splitting :
    ¬ (∀ (n : Nat) (W : WorldT n) (v : Val),
        arrowT nulT uT n W v → unionT (arrowT nulT nulT) (arrowT nulT boolT) n W v) := by
  intro hle
  rcases hle 5 (Wu 5) readCell (read_in_union 5) with h | h
  · exact read_not_in_nul h
  · exact read_not_in_bool h

/-! ## The representation: unions in operand position

A node's operands are sets of nodes, read as their union, and a type is a set of
nodes. Every operand still sits beneath a `ref` or an `arr`, so the guardedness
argument and the tower are exactly as before. -/

inductive Node (ι : Type) where
  | nul | bool
  | ref (a : List ι)
  | arr (a b : List ι)

abbrev Graph (ι : Type) := ι → Node ι

/-- A set of nodes denotes the union of its members. -/
def setSem {ι : Type} (X : ι → Fam) (S : List ι) : Fam := fun n W v => ∃ i ∈ S, X i n W v

def nodeSem {ι : Type} (X : ι → Fam) : Node ι → Fam
  | .nul => nulT
  | .bool => boolT
  | .ref a => refT (setSem X a)
  | .arr a b => arrowT (setSem X a) (setSem X b)

def layer {ι : Type} (G : Graph ι) (X : ι → Fam) (i : ι) : Fam := nodeSem X (G i)

theorem setSem_congr {ι : Type} {X Y : ι → Fam} (n : Nat)
    (h : ∀ i, Agree (X i) (Y i) n) (S : List ι) : Agree (setSem X S) (setSem Y S) n := by
  intro m hm W v
  constructor <;> rintro ⟨i, hi, hd⟩
  · exact ⟨i, hi, (h i m hm W v).mp hd⟩
  · exact ⟨i, hi, (h i m hm W v).mpr hd⟩

theorem layer_congr {ι : Type} (G : Graph ι) (X Y : ι → Fam) (n : Nat)
    (h : ∀ i, Agree (X i) (Y i) n) (i : ι) (W : WorldT n) (v : Val) :
    layer G X i n W v ↔ layer G Y i n W v := by
  unfold layer
  cases G i with
  | nul => rfl
  | bool => rfl
  | ref a => exact refT_contractive n _ _ (setSem_congr n h a) W v
  | arr a b =>
    exact (arrowT_contractive _ n _ _ (setSem_congr n h a) W v).trans
      (arrowT_cod_contractive _ n _ _ (setSem_congr n h b) W v)

def approx {ι : Type} (G : Graph ι) : Nat → ι → Fam
  | 0 => fun _ => topF
  | k + 1 => layer G (approx G k)

theorem approx_stable {ι : Type} (G : Graph ι) (n : Nat) :
    ∀ k l, n < k → n < l → ∀ (i : ι) (W : WorldT n) (v : Val),
      approx G k i n W v ↔ approx G l i n W v := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k l hk hl i W v
    cases k with
    | zero => omega
    | succ k =>
      cases l with
      | zero => omega
      | succ l =>
        exact layer_congr G _ _ n (fun a m hm U u =>
          ih m hm k l (by omega) (by omega) a U u) i W v

def denote {ι : Type} (G : Graph ι) (i : ι) : Fam := fun n => approx G (n + 1) i n

theorem denote_unfold {ι : Type} (G : Graph ι) (i : ι) (n : Nat) (W : WorldT n) (v : Val) :
    denote G i n W v ↔ layer G (denote G) i n W v :=
  layer_congr G _ _ n
    (fun a m hm U u => approx_stable G m n (m + 1) hm (by omega) a U u) i W v

/-- A type is a set of nodes. -/
def denoteSet {ι : Type} (G : Graph ι) (S : List ι) : Fam := setSem (denote G) S

/-! ## Admissibility -/

theorem setSem_adm {ι : Type} {X : ι → Fam} (h : ∀ i, Adm (X i)) (S : List ι) :
    Adm (setSem X S) := by
  constructor
  · rintro n W v ⟨i, hi, hd⟩; exact ⟨i, hi, (h i).down n W v hd⟩
  · rintro n W W' hx v ⟨i, hi, hd⟩; exact ⟨i, hi, (h i).mono n W W' hx v hd⟩

theorem nodeSem_adm {ι : Type} {X : ι → Fam} (_h : ∀ i, Adm (X i)) (N : Node ι) :
    Adm (nodeSem X N) := by
  cases N with
  | nul => exact nulT_adm
  | bool => exact boolT_adm
  | ref a => exact refT_adm _
  | arr a b => exact arrowT_adm _ _

theorem approx_adm {ι : Type} (G : Graph ι) : ∀ k i, Adm (approx G k i)
  | 0, _ => topF_adm
  | k + 1, i => nodeSem_adm (approx_adm G k) (G i)

theorem denote_adm {ι : Type} (G : Graph ι) (i : ι) : Adm (denote G i) := by
  constructor
  · intro n W v hv
    have h1 := (approx_adm G (n + 2) i).down n W v hv
    exact (approx_stable G n (n + 2) (n + 1) (by omega) (by omega) i _ v).mp h1
  · intro n W W' hx v hv
    exact (approx_adm G (n + 1) i).mono n W W' hx v hv

theorem denoteSet_adm {ι : Type} (G : Graph ι) (S : List ι) : Adm (denoteSet G S) :=
  setSem_adm (denote_adm G) S

/-! ### Well-formedness

A cell declared to hold nothing cannot appear in any heap, so `ref never` is a
type no program can inhabit — and worse, it is *invisible* to an arrow, whose
obligation over such a domain is vacuous. Chasing that exactly is a treadmill:
`ref never` is unreachable above budget 0, `ref (ref never)` above budget 1, and
since an arrow demands nothing below budget 2 (`Safe_app_one`) both are
invisible while `ref (ref (ref never))` is not. The side condition would have to
count evaluation steps, which is an artifact of the model rather than anything
about types.

So exclude them instead. Forbidding the single shape `ref never` removes the
whole hierarchy, because each level needs the one below it as a node. The cost
is a restriction the source language can live with: a well-formed program can
never allocate such a cell.

What remains is the *obvious* vacuity — an empty union — which is one syntactic
check on each operand, and which `arr_empty_dom` shows is genuinely needed. -/

def WF {ι : Type} (G : Graph ι) : Prop := ∀ i, G i ≠ Node.ref []

/-! ## Every well-formed clause is inhabited

`WF` earns its keep only if the clauses it admits are all *visible* to an arrow —
that is, inhabited at the budgets where an arrow constrains. The three atomic
shapes are inhabited in *any* world; a reference is inhabited only in a world
that declares the cell, so the argument is completed by building one world and
one heap that work for the whole graph at once. That is `wf_inhabited`. -/

theorem nodeSem_valOnly {ι : Type} (X : ι → Fam) (N : Node ι) : ValOnly (nodeSem X N) := by
  cases N with
  | nul => exact nulT_valOnly
  | bool => exact boolT_valOnly
  | ref a => exact refT_valOnly _
  | arr a b => exact arrowT_valOnly _ _

theorem denote_valOnly {ι : Type} (G : Graph ι) (i : ι) : ValOnly (denote G i) :=
  fun n W v hv => nodeSem_valOnly (denote G) (G i) n W v ((denote_unfold G i n W v).mp hv)

theorem denoteSet_valOnly {ι : Type} (G : Graph ι) (S : List ι) : ValOnly (denoteSet G S) := by
  rintro n W v ⟨i, -, hd⟩
  exact denote_valOnly G i n W v hd

theorem nul_inhabited {ι : Type} (G : Graph ι) (i : ι) (hG : G i = Node.nul)
    (n : Nat) (W : WorldT n) : denote G i n W .nul :=
  (denote_unfold G i n W _).mpr (by unfold layer; rw [hG]; rfl)

theorem bool_inhabited {ι : Type} (G : Graph ι) (i : ι) (hG : G i = Node.bool)
    (n : Nat) (W : WorldT n) : denote G i n W .tru :=
  (denote_unfold G i n W _).mpr (by unfold layer; rw [hG]; exact Or.inl rfl)

/-- **Every arrow clause is inhabited, in every world**, by the function that
ignores its argument and diverges. So no arrow clause is ever invisible. -/
theorem arr_inhabited {ι : Type} (G : Graph ι) (i : ι) (a b : List ι)
    (hG : G i = Node.arr a b) (n : Nat) (W : WorldT n) :
    denote G i n W (.lam omegaTm) := by
  refine (denote_unfold G i n W _).mpr ?_
  unfold layer; rw [hG]
  refine ⟨⟨omegaTm, rfl⟩, ?_⟩
  intro m _ W' _ hadm hp hok x hx
  exact ignore_safe _ m W' hp hadm hok x (denoteSet_valOnly G a m W' x hx)

/-! ### The canonical world

For a finite graph, one cell per operand set occurring in it, holding that
set's meaning. Reference operands need cells so that reference values exist at
all; arrow operands need them too, because the value that tells two arrow
domains apart works by writing its argument into a cell declared at the domain.
Empty operands get no cell, since no value could fill one. -/

def findIdx' {α : Type} [DecidableEq α] : List α → α → Nat
  | [], _ => 0
  | b :: l, a => if b = a then 0 else findIdx' l a + 1

theorem findIdx'_get {α : Type} [DecidableEq α] :
    ∀ (l : List α) (a : α), a ∈ l → l[findIdx' l a]? = some a := by
  intro l
  induction l with
  | nil => intro a ha; exact absurd ha (by simp)
  | cons b l ih =>
    intro a ha
    by_cases h : b = a
    · subst h; simp [findIdx']
    · have ha' : a ∈ l := by
        rcases List.mem_cons.mp ha with rfl | h'
        · exact absurd rfl h
        · exact h'
      simp only [findIdx', if_neg h, List.getElem?_cons_succ]
      exact ih a ha'

/-- Every operand set occurring in the graph, with the empty ones dropped. -/
def opSets {m : Nat} (G : Graph (Fin m)) : List (List (Fin m)) :=
  ((List.finRange m).flatMap fun i =>
    match G i with
    | .nul => []
    | .bool => []
    | .ref a => [a]
    | .arr a b => [a, b]).filter fun s => !s.isEmpty

theorem opSets_ne {m : Nat} {G : Graph (Fin m)} {a : List (Fin m)}
    (ha : a ∈ opSets G) : a ≠ [] := by
  simp only [opSets, List.mem_filter] at ha
  intro h; subst h; simp at ha

theorem opSets_ref {m : Nat} {G : Graph (Fin m)} {i : Fin m} {a : List (Fin m)}
    (hG : G i = Node.ref a) (hne : a ≠ []) : a ∈ opSets G := by
  simp only [opSets, List.mem_filter, List.mem_flatMap]
  refine ⟨⟨i, List.mem_finRange i, ?_⟩, by simp [hne]⟩
  rw [hG]; simp

theorem opSets_dom {m : Nat} {G : Graph (Fin m)} {i : Fin m} {a b : List (Fin m)}
    (hG : G i = Node.arr a b) (hne : a ≠ []) : a ∈ opSets G := by
  simp only [opSets, List.mem_filter, List.mem_flatMap]
  refine ⟨⟨i, List.mem_finRange i, ?_⟩, by simp [hne]⟩
  rw [hG]; simp

theorem opSets_cod {m : Nat} {G : Graph (Fin m)} {i : Fin m} {a b : List (Fin m)}
    (hG : G i = Node.arr a b) (hne : b ≠ []) : b ∈ opSets G := by
  simp only [opSets, List.mem_filter, List.mem_flatMap]
  refine ⟨⟨i, List.mem_finRange i, ?_⟩, by simp [hne]⟩
  rw [hG]; simp

theorem findIdx'_lt {α : Type} [DecidableEq α] {l : List α} {a : α} (h : a ∈ l) :
    findIdx' l a < l.length :=
  (List.getElem?_eq_some_iff.mp (findIdx'_get l a h)).1

/-- **Two** cells per operand set, not one. A single separating function has to
observe an arrow's domain and its codomain at the same time, by writing into the
first and reading from the second; if the two operands happen to be the same set
they would otherwise share a cell, and the write would destroy the reading. -/
def cells {m : Nat} (G : Graph (Fin m)) : List (List (Fin m)) := opSets G ++ opSets G

theorem cells_mem {m : Nat} {G : Graph (Fin m)} {a : List (Fin m)}
    (ha : a ∈ cells G) : a ∈ opSets G := by
  rcases List.mem_append.mp ha with h | h <;> exact h

/-- The cell a value is written into, and the cell a result is read from. -/
def cellA {m : Nat} (G : Graph (Fin m)) (a : List (Fin m)) : Nat := findIdx' (opSets G) a
def cellB {m : Nat} (G : Graph (Fin m)) (a : List (Fin m)) : Nat :=
  (opSets G).length + cellA G a

theorem cellA_ne_cellB {m : Nat} (G : Graph (Fin m)) {a b : List (Fin m)}
    (ha : a ∈ opSets G) : cellA G a ≠ cellB G b := by
  intro he
  have h1 := findIdx'_lt ha
  simp only [cellA, cellB] at he
  omega

/-- Each declared cell holds the meaning of its operand set. -/
def graphWorld {m : Nat} (G : Graph (Fin m)) (n : Nat) : WorldT n :=
  ofList ((cells G).map fun a => res (denoteSet G a))

theorem graphWorld_lookup {m : Nat} (G : Graph (Fin m)) (n : Nat) {a : List (Fin m)}
    (ha : a ∈ opSets G) :
    lookup (graphWorld G n) (cellA G a) = some (res (denoteSet G a)) := by
  simp only [lookup, graphWorld, cells, cellA, toList_ofList, List.map_append]
  rw [List.getElem?_append_left (by simpa using findIdx'_lt ha)]
  rw [List.getElem?_map, findIdx'_get _ a ha]
  rfl

theorem graphWorld_lookupB {m : Nat} (G : Graph (Fin m)) (n : Nat) {a : List (Fin m)}
    (ha : a ∈ opSets G) :
    lookup (graphWorld G n) (cellB G a) = some (res (denoteSet G a)) := by
  simp only [lookup, graphWorld, cells, toList_ofList, List.map_append]
  rw [List.getElem?_append_right (by simp [cellB])]
  simp only [cellB, cellA, List.length_map, Nat.add_sub_cancel_left]
  rw [List.getElem?_map, findIdx'_get _ a ha]
  rfl

theorem graphWorld_trunc {m : Nat} (G : Graph (Fin m)) {n j : Nat} (h : j ≤ n) :
    trunc j h (graphWorld G n) = graphWorld G j := by
  simp only [graphWorld, trunc, toList_ofList, List.map_map]
  rfl

/-- Worlds that extend the canonical one: they keep every declared cell, so the
canonical values keep their meanings. -/
def Over {m : Nat} (G : Graph (Fin m)) (n : Nat) (U : WorldT n) : Prop :=
  WExt (graphWorld G n) U

theorem over_trunc {m : Nat} {G : Graph (Fin m)} {n j : Nat} {U : WorldT n}
    (hx : Over G n U) (hj : j ≤ n) : Over G j (trunc j hj U) := by
  have ht := WExt_trunc hj hx
  rwa [graphWorld_trunc] at ht

theorem over_ext {m : Nat} {G : Graph (Fin m)} {n : Nat} {U V : WorldT n}
    (hx : Over G n U) (hy : WExt U V) : Over G n V := WExt_trans hx hy

theorem graphWorld_adm {m : Nat} (G : Graph (Fin m)) (n : Nat) :
    WorldAdm (graphWorld G n) := by
  intro l c hl
  simp only [lookup, graphWorld, toList_ofList, List.getElem?_map] at hl
  rcases hs : (cells G)[l]? with _ | a
  · rw [hs] at hl; simp at hl
  · rw [hs] at hl
    simp only [Option.map_some, Option.some.injEq] at hl
    subst hl
    exact fun j _ U U' hx v hv => (denoteSet_adm G a).mono j U U' hx v hv

/-! ### The canonical value of a clause -/

def canonClause {m : Nat} (G : Graph (Fin m)) (i : Fin m) : Val :=
  match G i with
  | .nul => .nul
  | .bool => .tru
  | .ref a => .loc (cellA G a)
  | .arr _ _ => .lam omegaTm

def canon {m : Nat} (G : Graph (Fin m)) : List (Fin m) → Val
  | [] => .nul
  | i :: _ => canonClause G i

theorem canonLoc_mem {m : Nat} (G : Graph (Fin m)) {i : Fin m} {a : List (Fin m)}
    (hG : G i = Node.ref a) (hne : a ≠ []) (n : Nat) (U : WorldT n) (ho : Over G n U) :
    denote G i n U (.loc (cellA G a)) := by
  refine (denote_unfold G i n U _).mpr ?_
  unfold layer; rw [hG]
  exact ⟨_, res (denoteSet G a), rfl,
    WExt_lookup ho (graphWorld_lookup G n (opSets_ref hG hne)), fun _ _ _ _ => Iff.rfl⟩

/-- **The canonical value of a clause inhabits it in every world over the
canonical one.** For the atoms and the arrows any world will do; a reference
needs its cell, which is what `Over` keeps. -/
theorem canonClause_over {m : Nat} (G : Graph (Fin m)) (hwf : WF G) (i : Fin m)
    (n : Nat) (U : WorldT n) (ho : Over G n U) :
    denote G i n U (canonClause G i) := by
  unfold canonClause
  cases hG : G i with
  | nul => exact nul_inhabited G i hG n _
  | bool => exact bool_inhabited G i hG n _
  | arr a b => exact arr_inhabited G i a b hG n _
  | ref a => exact canonLoc_mem G hG (fun hz => hwf i (hz ▸ hG)) n U ho

theorem canon_over {m : Nat} (G : Graph (Fin m)) (hwf : WF G) (a : List (Fin m))
    (ha : a ≠ []) (n : Nat) (U : WorldT n) (ho : Over G n U) :
    denoteSet G a n U (canon G a) := by
  cases a with
  | nil => exact absurd rfl ha
  | cons i l => exact ⟨i, by simp, canonClause_over G hwf i n U ho⟩

theorem canonClause_mem {m : Nat} (G : Graph (Fin m)) (hwf : WF G) (i : Fin m) (n : Nat) :
    denote G i n (graphWorld G n) (canonClause G i) :=
  canonClause_over G hwf i n _ (WExt_refl _)

theorem canon_mem {m : Nat} (G : Graph (Fin m)) (hwf : WF G) (a : List (Fin m))
    (ha : a ≠ []) (n : Nat) : denoteSet G a n (graphWorld G n) (canon G a) :=
  canon_over G hwf a ha n _ (WExt_refl _)

/-! ### The canonical heap

And this is where `WF` is needed, rather than merely tidy: a cell declared for
`ref never` has no value to hold, so without the restriction no heap satisfies
the canonical world. -/

def graphHeap {m : Nat} (G : Graph (Fin m)) : Heap := (cells G).map (canon G)

theorem graphHeap_ok {m : Nat} (G : Graph (Fin m)) (hwf : WF G) (n : Nat) :
    HeapOk n (graphWorld G n) (graphHeap G) := by
  refine ⟨by simp [graphHeap, graphWorld], ?_⟩
  intro l c hl
  simp only [lookup, graphWorld, toList_ofList, List.getElem?_map] at hl
  rcases hs : (cells G)[l]? with _ | a
  · rw [hs] at hl; simp at hl
  · rw [hs] at hl
    simp only [Option.map_some, Option.some.injEq] at hl
    subst hl
    have hane : a ≠ [] := opSets_ne (cells_mem (List.mem_of_getElem? hs))
    refine ⟨canon G a, by simp only [graphHeap, List.getElem?_map, hs]; rfl, ?_⟩
    intro j hj
    show denoteSet G a j _ (canon G a)
    rw [graphWorld_trunc]
    exact canon_mem G hwf a hane j

/-- **Inhabitation.** In a well-formed graph every non-empty clause set is
inhabited at every budget — and not vacuously so: the world it is inhabited in
is one that an actual heap satisfies, so the witness is a value a running
program could hold. -/
theorem wf_inhabited {m : Nat} (G : Graph (Fin m)) (hwf : WF G) (a : List (Fin m))
    (ha : a ≠ []) (n : Nat) :
    ∃ (W : WorldT n) (h : Heap) (v : Val), HeapOk n W h ∧ denoteSet G a n W v :=
  ⟨graphWorld G n, graphHeap G, canon G a, graphHeap_ok G hwf n, canon_mem G hwf a ha n⟩

/-! ## Covering

Every clause of the source must be matched by a clause of the target: the atoms
by presence, references invariantly, arrows contravariantly. Operands are now
sets, so a union under a constructor is compared as a whole rather than being
hoisted — which is what `ref A ∨ ref B ≠ ref (A ∨ B)` forces. -/

def hasNul {ι : Type} (G : Graph ι) (S : List ι) : Prop := ∃ i ∈ S, G i = Node.nul
def hasBool {ι : Type} (G : Graph ι) (S : List ι) : Prop := ∃ i ∈ S, G i = Node.bool

def refOps {ι : Type} (G : Graph ι) (S : List ι) : List (List ι) :=
  S.filterMap fun i => match G i with | .ref a => some a | _ => none

def arrOps {ι : Type} (G : Graph ι) (S : List ι) : List (List ι × List ι) :=
  S.filterMap fun i => match G i with | .arr a b => some (a, b) | _ => none

/-! ### Why the reference rule is invariant

Nothing about references is *assumed* below: the semantics forces the rule. A
location carries the contract the world declares for it, and membership in
`ref b` asks that contract to *agree* with `⟦b⟧`, not merely to imply it. So one
reference is below another only when the two operands denote the same family —
and, `WF` having ruled out the empty cell, that is a real constraint rather than
one two vacuous types could both satisfy. -/
theorem ref_invariance_forced {m : Nat} (G : Graph (Fin m)) (hwf : WF G) {i j : Fin m}
    {a b : List (Fin m)} (hi : G i = Node.ref a) (hj : G j = Node.ref b) (n : Nat)
    (hsub : ∀ v : Val, denote G i n (graphWorld G n) v → denote G j n (graphWorld G n) v) :
    ∀ (k : Nat), k < n → ∀ (W : WorldT k) (u : Val),
      denoteSet G a k W u ↔ denoteSet G b k W u := by
  have hstep := hsub _ (canonClause_mem G hwf i n)
  rw [denote_unfold] at hstep
  unfold layer at hstep; rw [hj] at hstep
  obtain ⟨l, c, hloc, hlk, hc⟩ := hstep
  have hcan : canonClause G i = Tm.loc (cellA G a) := by
    unfold canonClause; rw [hi]
  rw [hcan] at hloc
  injection hloc with hl
  subst hl
  have hne : a ≠ [] := fun h => hwf i (h ▸ hi)
  rw [graphWorld_lookup G n (opSets_ref hi hne)] at hlk
  injection hlk with hcres
  subst hcres
  intro k hk W u
  exact hc k hk W u

/-- Every clause of the source must be matched by a clause of the target: atoms
by presence, references invariantly, arrows contravariantly. An operand that is
an empty union waives the comparison on the other side, since then no argument
can be supplied, or no result returned. -/
def Cover {ι : Type} (G : Graph ι) (R : List ι → List ι → Prop) (S T : List ι) : Prop :=
  (hasNul G S → hasNul G T) ∧
  (hasBool G S → hasBool G T) ∧
  (∀ a ∈ refOps G S, ∃ b ∈ refOps G T, R a b ∧ R b a) ∧
  (∀ a b, (a, b) ∈ arrOps G S →
    ∃ c d, (c, d) ∈ arrOps G T ∧ (c = [] ∨ (R c a ∧ (b = [] ∨ R b d))))

def SimRel {ι : Type} (G : Graph ι) (R : List ι → List ι → Prop) : Prop :=
  ∀ S T, R S T → Cover G R S T

/-- A cyclic covering certificate: `S` is below `T`. -/
def Sim {ι : Type} (G : Graph ι) (S T : List ι) : Prop := ∃ R, SimRel G R ∧ R S T

/-! ### Reading clauses back -/

theorem node_mem {ι : Type} {G : Graph ι} {S : List ι} {i : ι} (hi : i ∈ S)
    (n : Nat) (W : WorldT n) (v : Val) (h : layer G (denote G) i n W v) :
    denoteSet G S n W v := ⟨i, hi, (denote_unfold G i n W v).mpr h⟩

theorem mem_refOps {ι : Type} {G : Graph ι} {S : List ι} {i : ι} {a : List ι}
    (hi : i ∈ S) (hG : G i = .ref a) : a ∈ refOps G S := by
  simp only [refOps, List.mem_filterMap]
  exact ⟨i, hi, by rw [hG]⟩

theorem mem_arrOps {ι : Type} {G : Graph ι} {S : List ι} {i : ι} {a b : List ι}
    (hi : i ∈ S) (hG : G i = .arr a b) : (a, b) ∈ arrOps G S := by
  simp only [arrOps, List.mem_filterMap]
  exact ⟨i, hi, by rw [hG]⟩

theorem refOps_mem {ι : Type} {G : Graph ι} {T : List ι} {b : List ι}
    (hb : b ∈ refOps G T) : ∃ i ∈ T, G i = .ref b := by
  simp only [refOps, List.mem_filterMap] at hb
  obtain ⟨i, hi, he⟩ := hb
  refine ⟨i, hi, ?_⟩
  cases hG : G i <;> rw [hG] at he <;> simp at he
  rw [he]

theorem arrOps_mem {ι : Type} {G : Graph ι} {T : List ι} {c d : List ι}
    (hcd : (c, d) ∈ arrOps G T) : ∃ i ∈ T, G i = .arr c d := by
  simp only [arrOps, List.mem_filterMap] at hcd
  obtain ⟨i, hi, he⟩ := hcd
  refine ⟨i, hi, ?_⟩
  cases hG : G i <;> rw [hG] at he <;> simp at he
  rw [he.1, he.2]

/-- The justification for `WF`. No satisfying heap admits a value at `ref never`
above budget zero: the cell would have to hold something, and nothing qualifies.
An arrow over such a domain therefore demands nothing. -/
theorem vac_clause_empty {ι : Type} {G : Graph ι} {i : ι} (hG : G i = Node.ref [])
    (m : Nat) (hm : 0 < m) (W : WorldT m) (h : Heap) (hok : HeapOk m W h) (x : Val) :
    ¬ denote G i m W x := by
  intro hd
  have hd' := (denote_unfold G i m W x).mp hd
  unfold layer at hd'
  rw [hG] at hd'
  obtain ⟨l, c, rfl, hl, hag⟩ := hd'
  obtain ⟨v, -, hmem⟩ := hok.2 l c hl
  rcases (hag 0 hm (trunc 0 (Nat.le_of_lt hm) W) v).mp (hmem 0 hm) with ⟨k, hk, -⟩
  simp at hk

theorem WorldAdm_zero (W : WorldT 0) : WorldAdm W :=
  fun _ _ _ j hj => absurd hj (by omega)

/-- And the other half of the justification: an arrow demands nothing below
budget two. An application is not a value, it beta-steps, and what remains is
budget zero, where everything is safe. -/
theorem Safe_app_one (B : Fam) (b x : Tm) (hx : isVal x = true)
    (W : WorldT 1) (h : Heap) (hok : HeapOk 1 W h) :
    Safe B 1 W h (.app (.lam b) x) :=
  Or.inr ⟨trunc 0 (by omega) W, h, subst 0 x b, WExt_refl _, WorldAdm_zero _,
    .beta hx, HeapOk_trunc 0 W h hok, trivial⟩

/-! ### Soundness -/

theorem sim_sound {ι : Type} (G : Graph ι) (R : List ι → List ι → Prop) (hR : SimRel G R) :
    ∀ (n : Nat) (S T : List ι), R S T → ∀ (W : WorldT n) (v : Val),
      denoteSet G S n W v → denoteSet G T n W v := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro S T hST W v hv
    obtain ⟨i, hi, hd⟩ := hv
    have hd' := (denote_unfold G i n W v).mp hd
    obtain ⟨hnul, hbool, href, harr⟩ := hR S T hST
    unfold layer at hd'
    cases hG : G i <;> rw [hG] at hd'
    · obtain ⟨j, hj, hGj⟩ := hnul ⟨i, hi, hG⟩
      exact node_mem hj n W v (by unfold layer; rw [hGj]; exact hd')
    · obtain ⟨j, hj, hGj⟩ := hbool ⟨i, hi, hG⟩
      exact node_mem hj n W v (by unfold layer; rw [hGj]; exact hd')
    · rename_i a
      obtain ⟨b, hb, hab, hba⟩ := href a (mem_refOps hi hG)
      obtain ⟨j, hj, hGj⟩ := refOps_mem hb
      obtain ⟨l, c, rfl, hl, hag⟩ := hd'
      refine node_mem hj n W _ ?_
      unfold layer; rw [hGj]
      refine ⟨l, c, rfl, hl, ?_⟩
      intro m hm W' u
      refine (hag m hm W' u).trans ⟨fun h => ?_, fun h => ?_⟩
      · exact ih m hm a b hab W' u h
      · exact ih m hm b a hba W' u h
    · rename_i a b
      obtain ⟨c, d, hcd, hcase⟩ := harr a b (mem_arrOps hi hG)
      obtain ⟨j, hj, hGj⟩ := arrOps_mem hcd
      obtain ⟨hlam, hf⟩ := hd'
      refine node_mem hj n W v ?_
      unfold layer; rw [hGj]
      refine ⟨hlam, ?_⟩
      intro m hm W' hW hadm hp hok x hx
      rcases hcase with rfl | ⟨hca, hbd⟩
      · obtain ⟨k, hk, -⟩ := hx
        simp at hk
      · have hsafe := hf m hm W' hW hadm hp hok x (ih m hm c a hca W' x hx)
        rcases hbd with rfl | hbd
        · exact Safe_mono m (fun q _ U u hu => absurd hu (by rintro ⟨k, hk, -⟩; simp at hk))
            W' hp _ hsafe
        · exact Safe_mono m (fun q hq U u hu => ih q (by omega) b d hbd U u hu) W' hp _
            hsafe

theorem Sim_sound {ι : Type} (G : Graph ι) {S T : List ι} (h : Sim G S T)
    (n : Nat) (W : WorldT n) (v : Val) (hv : denoteSet G S n W v) :
    denoteSet G T n W v := by
  obtain ⟨R, hR, hST⟩ := h
  exact sim_sound G R hR n S T hST W v hv

/-! ## Completeness: from semantic inclusion back to covering

Soundness says a covering certificate implies inclusion. The converse asks for
the certificate to be *found* whenever inclusion holds, and the only way to find
it is to show that a missing clause is observable: if the target has no clause
matching some clause of the source, then some value witnesses the difference.

The witness is a closed value that lies in the source at every world over the
canonical one, and fails the target — the whole target, not one clause of it —
in every admissible, inhabited extension above a finite budget. That is `Sep`,
and `sep_not_incl` is why it is the right notion: a separating value refutes
inclusion outright.

The union shows up in the negative half. A single value must escape *every*
clause of the target at once, so the thresholds of the individual failures are
combined by `sep_of_clauses`, which is where the finiteness of a type as a list
of clauses is used. -/

/-- `S` is separated from `T`: one closed value inhabits `S` everywhere over the
canonical world, and escapes `T` everywhere above some budget. -/
def Sep {m : Nat} (G : Graph (Fin m)) (S T : List (Fin m)) : Prop :=
  ∃ (v : Val) (N : Nat), Closed v ∧
    (∀ n U, Over G n U → denoteSet G S n U v) ∧
    (∀ n, N ≤ n → ∀ (U : WorldT n) (h : Heap), Over G n U → WorldAdm U → HeapOk n U h →
      ¬ denoteSet G T n U v)

theorem sep_not_incl {m : Nat} (G : Graph (Fin m)) (hwf : WF G) {S T : List (Fin m)}
    (hs : Sep G S T) :
    ¬ (∀ (n : Nat) (W : WorldT n) (v : Val), denoteSet G S n W v → denoteSet G T n W v) := by
  rintro hincl
  obtain ⟨v, N, -, hp, hn⟩ := hs
  exact hn N (Nat.le_refl N) _ (graphHeap G) (WExt_refl _) (graphWorld_adm G N)
    (graphHeap_ok G hwf N) (hincl N _ v (hp N _ (WExt_refl _)))

/-! ### Each shape of value belongs to one shape of node

This is what makes the atomic clauses observable at all: a null can only be in a
`nul` clause, a location only in a `ref` clause, a lambda only in an `arr`
clause. -/

theorem denote_nul_shape {ι : Type} (G : Graph ι) {i : ι} {n : Nat} {W : WorldT n}
    (h : denote G i n W .nul) : G i = Node.nul := by
  have h' := (denote_unfold G i n W _).mp h
  unfold layer at h'
  cases hG : G i with
  | nul => rfl
  | bool => rw [hG] at h'; simp [nodeSem, boolT] at h'
  | ref a => rw [hG] at h'; simp [nodeSem, refT] at h'
  | arr a b => rw [hG] at h'; simp [nodeSem, arrowT] at h'

theorem denote_tru_shape {ι : Type} (G : Graph ι) {i : ι} {n : Nat} {W : WorldT n}
    (h : denote G i n W .tru) : G i = Node.bool := by
  have h' := (denote_unfold G i n W _).mp h
  unfold layer at h'
  cases hG : G i with
  | nul => rw [hG] at h'; simp [nodeSem, nulT] at h'
  | bool => rfl
  | ref a => rw [hG] at h'; simp [nodeSem, refT] at h'
  | arr a b => rw [hG] at h'; simp [nodeSem, arrowT] at h'

theorem denote_loc_shape {ι : Type} (G : Graph ι) {i : ι} {n : Nat} {W : WorldT n} {l : Nat}
    (h : denote G i n W (.loc l)) : ∃ a, G i = Node.ref a := by
  have h' := (denote_unfold G i n W _).mp h
  unfold layer at h'
  cases hG : G i with
  | nul => rw [hG] at h'; simp [nodeSem, nulT] at h'
  | bool => rw [hG] at h'; simp [nodeSem, boolT] at h'
  | ref a => exact ⟨a, rfl⟩
  | arr a b => rw [hG] at h'; simp [nodeSem, arrowT] at h'

theorem denote_lam_shape {ι : Type} (G : Graph ι) {i : ι} {n : Nat} {W : WorldT n} {b : Tm}
    (h : denote G i n W (.lam b)) : ∃ c d, G i = Node.arr c d := by
  have h' := (denote_unfold G i n W _).mp h
  unfold layer at h'
  cases hG : G i with
  | nul => rw [hG] at h'; simp [nodeSem, nulT] at h'
  | bool => rw [hG] at h'; simp [nodeSem, boolT] at h'
  | ref a => rw [hG] at h'; simp [nodeSem, refT] at h'
  | arr c d => exact ⟨c, d, rfl⟩

/-! ### Combining clause failures

A separating value has to escape the whole target, so the budgets above which it
escapes each clause are combined into one. The list of clauses being finite is
exactly what makes that possible. -/

theorem sep_of_clauses {m : Nat} (G : Graph (Fin m)) (v : Val) (T : List (Fin m))
    (h : ∀ j ∈ T, ∃ N, ∀ n, N ≤ n → ∀ (U : WorldT n) (hp : Heap),
      Over G n U → WorldAdm U → HeapOk n U hp → ¬ denote G j n U v) :
    ∃ N, ∀ n, N ≤ n → ∀ (U : WorldT n) (hp : Heap),
      Over G n U → WorldAdm U → HeapOk n U hp → ¬ denoteSet G T n U v := by
  induction T with
  | nil =>
    refine ⟨0, ?_⟩
    rintro n - U hp - - - ⟨j, hj, -⟩
    simp at hj
  | cons j T ih =>
    obtain ⟨N1, h1⟩ := h j (List.mem_cons_self ..)
    obtain ⟨N2, h2⟩ := ih (fun k hk => h k (List.mem_cons_of_mem _ hk))
    refine ⟨max N1 N2, ?_⟩
    rintro n hn U hp ho hu hh ⟨k, hk, hd⟩
    rcases List.mem_cons.mp hk with rfl | hk'
    · exact h1 n (Nat.le_trans (Nat.le_max_left _ _) hn) U hp ho hu hh hd
    · exact h2 n (Nat.le_trans (Nat.le_max_right _ _) hn) U hp ho hu hh ⟨k, hk', hd⟩

/-! ### The atomic clauses -/

theorem sep_nul {m : Nat} (G : Graph (Fin m)) {S T : List (Fin m)}
    (hS : hasNul G S) (hT : ¬ hasNul G T) : Sep G S T := by
  obtain ⟨i, hi, hG⟩ := hS
  refine ⟨.nul, 0, by intro k a; rfl, ?_, ?_⟩
  · intro n U _
    exact node_mem hi n U _ (by unfold layer; rw [hG]; rfl)
  · rintro n - U hp - - - ⟨j, hj, hd⟩
    exact hT ⟨j, hj, denote_nul_shape G hd⟩

theorem sep_bool {m : Nat} (G : Graph (Fin m)) {S T : List (Fin m)}
    (hS : hasBool G S) (hT : ¬ hasBool G T) : Sep G S T := by
  obtain ⟨i, hi, hG⟩ := hS
  refine ⟨.tru, 0, by intro k a; rfl, ?_, ?_⟩
  · intro n U _
    exact node_mem hi n U _ (by unfold layer; rw [hG]; exact Or.inl rfl)
  · rintro n - U hp - - - ⟨j, hj, hd⟩
    exact hT ⟨j, hj, denote_tru_shape G hd⟩

/-! ### The reference clauses

A reference clause is observable through the canonical location of its operand.
The location lies in the source at every world over the canonical one, and a
target clause can accept it only by being a reference whose operand denotes the
*same* family — so a target that has no such clause is escaped, and the escape
is witnessed at whatever world and budget the families already differ at. -/

/-- Two operand sets whose meanings differ somewhere. -/
def FamDiff {m : Nat} (G : Graph (Fin m)) (a b : List (Fin m)) : Prop :=
  ∃ (N : Nat) (V : WorldT N) (w : Val), ¬ (denoteSet G a N V w ↔ denoteSet G b N V w)

theorem sep_famDiff {m : Nat} (G : Graph (Fin m)) (hwf : WF G) {a b : List (Fin m)}
    (hs : Sep G a b) : FamDiff G a b := by
  obtain ⟨v, N, -, hp, hn⟩ := hs
  refine ⟨N, graphWorld G N, v, ?_⟩
  intro he
  exact hn N (Nat.le_refl N) _ (graphHeap G) (WExt_refl _) (graphWorld_adm G N)
    (graphHeap_ok G hwf N) (he.mp (hp N _ (WExt_refl _)))

theorem famDiff_symm {m : Nat} (G : Graph (Fin m)) {a b : List (Fin m)}
    (h : FamDiff G a b) : FamDiff G b a := by
  obtain ⟨N, V, w, hd⟩ := h
  exact ⟨N, V, w, fun he => hd he.symm⟩

theorem loc_escapes_clause {m : Nat} (G : Graph (Fin m)) {a : List (Fin m)}
    (haOp : a ∈ opSets G) (j : Fin m) (h : ∀ b, G j = Node.ref b → FamDiff G a b) :
    ∃ N, ∀ n, N ≤ n → ∀ (U : WorldT n) (hp : Heap),
      Over G n U → WorldAdm U → HeapOk n U hp →
        ¬ denote G j n U (.loc (cellA G a)) := by
  cases hG : G j with
  | nul =>
    exact ⟨0, fun n _ U _ _ _ _ hd => by
      obtain ⟨c, hc⟩ := denote_loc_shape G hd; rw [hG] at hc; exact absurd hc (by simp)⟩
  | bool =>
    exact ⟨0, fun n _ U _ _ _ _ hd => by
      obtain ⟨c, hc⟩ := denote_loc_shape G hd; rw [hG] at hc; exact absurd hc (by simp)⟩
  | arr c d =>
    exact ⟨0, fun n _ U _ _ _ _ hd => by
      obtain ⟨e, he⟩ := denote_loc_shape G hd; rw [hG] at he; exact absurd he (by simp)⟩
  | ref b =>
    obtain ⟨N, V, w, hbad⟩ := h b hG
    refine ⟨N + 1, ?_⟩
    intro n hn U hp ho _ _ hd
    have hd' := (denote_unfold G j n U _).mp hd
    unfold layer at hd'; rw [hG] at hd'
    obtain ⟨l, c, he, hl, hc⟩ := hd'
    cases he
    have ha := WExt_lookup ho (graphWorld_lookup G n haOp)
    rw [ha] at hl
    cases hl
    exact hbad (hc N (by omega) V w)

/-- **The reference clause of covering is forced.** If the source has a `ref a`
clause and no reference clause of the target denotes the same family, the
canonical location of `a` separates the two types. -/
theorem sep_of_ref_unmatched {m : Nat} (G : Graph (Fin m)) (hwf : WF G)
    {S T : List (Fin m)} {a : List (Fin m)} (ha : a ∈ refOps G S)
    (h : ∀ b ∈ refOps G T, FamDiff G a b) : Sep G S T := by
  obtain ⟨i, hi, hG⟩ := refOps_mem ha
  have hne : a ≠ [] := fun hz => hwf i (hz ▸ hG)
  obtain ⟨N, hN⟩ := sep_of_clauses G (.loc (cellA G a)) T
    (fun j hj => loc_escapes_clause G (opSets_ref hG hne) j
      (fun b hb => h b (mem_refOps hj hb)))
  exact ⟨_, N, by intro k x; rfl,
    fun n U ho => ⟨i, hi, canonLoc_mem G hG hne n U ho⟩, hN⟩

/-! ### The arrow clauses

An arrow is observed by a function that writes its argument into a cell declared
at the source domain and returns the contents of a cell declared at the source
codomain. A target clause can accept that function only if every argument it
admits can be written into the domain cell, and only if everything the codomain
cell may hold is a legal result. So one value observes both sides at once, which
is what a union in the target needs: a single value has to escape every clause.
The two cells are distinct even when the two operands coincide — that is what
the duplication in `cells` is for. -/

theorem probe_in_arrow {m : Nat} (G : Graph (Fin m)) {i : Fin m} {a b : List (Fin m)}
    (hG : G i = Node.arr a b) (haOp : a ∈ opSets G) (hbOp : b ∈ opSets G)
    (n : Nat) (U : WorldT n) (ho : Over G n U) :
    denote G i n U (probe (cellA G a) (cellB G b)) := by
  refine (denote_unfold G i n U _).mpr ?_
  unfold layer; rw [hG]
  exact probe_typed (denoteSet_adm G a) (denoteSet_valOnly G a) (denoteSet_valOnly G b)
    n U _ _
    ⟨_, _, rfl, WExt_lookup ho (graphWorld_lookup G n haOp), fun _ _ _ _ => Iff.rfl⟩
    ⟨_, _, rfl, WExt_lookup ho (graphWorld_lookupB G n hbOp), fun _ _ _ _ => Iff.rfl⟩

/-- **A domain the target admits and the source does not is observable.** The
probe writes its argument into the source's domain cell, so an argument outside
that cell's contract leaves a heap no world can satisfy. -/
theorem probe_escapes_dom {m : Nat} (G : Graph (Fin m)) {a b c d : List (Fin m)}
    {j : Fin m} (hG : G j = Node.arr c d) (haOp : a ∈ opSets G) (hs : Sep G c a) :
    ∃ N, ∀ n, N ≤ n → ∀ (U : WorldT n) (hp : Heap),
      Over G n U → WorldAdm U → HeapOk n U hp →
        ¬ denote G j n U (probe (cellA G a) (cellB G b)) := by
  obtain ⟨v, N, -, hpos, hneg⟩ := hs
  have hval : isVal v = true := denoteSet_valOnly G c 0 _ v (hpos 0 _ (WExt_refl _))
  refine ⟨N + 4, ?_⟩
  intro n hN U h ho hu hh hv
  have ht := (denote_unfold G j n U _).mp hv
  unfold layer at ht; rw [hG] at ht
  have hoV : Over G (N + 3) (trunc (N + 3) (by omega) U) := over_trunc ho (by omega)
  have hhV : HeapOk (N + 3) (trunc (N + 3) (by omega) U) h := heap_down hh (N + 3) (by omega)
  have huV : WorldAdm (trunc (N + 3) (by omega) U) :=
    WorldAdm_trunc (show N + 3 ≤ n by omega) hu
  have hsafe := ht.2 (N + 3) (by omega) _ (WExt_refl _) huV h hhV v (hpos _ _ hoV)
  rcases hsafe with ⟨hbad, -⟩ | ⟨Z, h', tm, hz, -, hstep, -, hst⟩
  · simp [isVal] at hbad
  obtain ⟨he, rfl⟩ := probe_step_inv hval hstep
  subst he
  have hoz := over_ext (over_trunc hoV (Nat.le_succ (N + 2))) hz
  rcases hst with ⟨hbad, -⟩ | ⟨Q, h'', t', hq, huq, hs', hhq, -⟩
  · simp [isVal] at hbad
  obtain ⟨he2, -, hlt⟩ := write_step_inv hval hs'
  subst he2
  have hoq := over_ext (over_trunc hoz (Nat.le_succ (N + 1))) hq
  have hl := WExt_lookup hoq (graphWorld_lookup G (N + 1) haOp)
  obtain ⟨w, hw, hm⟩ := hhq.2 (cellA G a) (res (denoteSet G a)) hl
  simp [hlt] at hw
  subst hw
  exact hneg N (Nat.le_refl N) _ _ (over_trunc hoq (Nat.le_succ N))
    (WorldAdm_trunc (Nat.le_succ N) huq) (HeapOk_trunc N Q _ hhq)
    (hm N (show N < N + 1 by omega))

/-- **A result the source may return and the target may not is observable.**
The probe returns whatever the source's codomain cell holds, and an arrow
quantifies over every satisfying heap, so an observer may put the offending
value in that cell before applying the function. This is the half that unions in
the codomain need, and the reason arrows do not split. -/
theorem probe_escapes_cod {m : Nat} (G : Graph (Fin m)) (hwf : WF G)
    {a b c d : List (Fin m)} {j : Fin m} (hG : G j = Node.arr c d)
    (haOp : a ∈ opSets G) (hbOp : b ∈ opSets G) (hcne : c ≠ []) (hs : Sep G b d) :
    ∃ N, ∀ n, N ≤ n → ∀ (U : WorldT n) (hp : Heap),
      Over G n U → WorldAdm U → HeapOk n U hp →
        ¬ denote G j n U (probe (cellA G a) (cellB G b)) := by
  obtain ⟨w, N, -, hpos, hneg⟩ := hs
  have hwval : isVal w = true := denoteSet_valOnly G b 0 _ w (hpos 0 _ (WExt_refl _))
  refine ⟨N + 6, ?_⟩
  intro n hN U hp ho hu hh hv
  have ht := (denote_unfold G j n U _).mp hv
  unfold layer at ht; rw [hG] at ht
  -- the world we run in, and the heap that holds the offending result
  have hoV : Over G (N + 5) (trunc (N + 5) (by omega) U) := over_trunc ho (by omega)
  have huV : WorldAdm (trunc (N + 5) (by omega) U) :=
    WorldAdm_trunc (show N + 5 ≤ n by omega) hu
  have hhV : HeapOk (N + 5) (trunc (N + 5) (by omega) U) hp := heap_down hh (N + 5) (by omega)
  have hlB := WExt_lookup hoV (graphWorld_lookupB G (N + 5) hbOp)
  have hokW : HeapOk (N + 5) (trunc (N + 5) (by omega) U) (hp.set (cellB G b) w) :=
    write_sound (N + 5) _ hp (cellB G b) _ w hhV hlB
      (fun k hk => hpos k _ (over_trunc hoV (Nat.le_of_lt hk)))
  have hsafe := ht.2 (N + 5) (by omega) _ (WExt_refl _) huV _ hokW (canon G c)
    (canon_over G hwf c hcne (N + 5) _ hoV)
  have hargval : isVal (canon G c) = true :=
    denoteSet_valOnly G c (N + 5) _ _ (canon_over G hwf c hcne (N + 5) _ hoV)
  -- beta
  rcases hsafe with ⟨hbad, -⟩ | ⟨Z, h1, t1, hz, huz, hst1, hok1, hs1⟩
  · simp [isVal] at hbad
  obtain ⟨he1, rfl⟩ := probe_step_inv hargval hst1
  subst he1
  have hoz := over_ext (over_trunc hoV (Nat.le_succ (N + 4))) hz
  -- the write
  rcases hs1 with ⟨hbad, -⟩ | ⟨Q, h2, t2, hq, huq, hst2, hok2, hs2⟩
  · simp [isVal] at hbad
  obtain ⟨he2, rfl, hlt⟩ := write_step_inv hargval hst2
  subst he2
  have hoq := over_ext (over_trunc hoz (Nat.le_succ (N + 3))) hq
  -- discard the null the write returned
  rcases hs2 with ⟨hbad, -⟩ | ⟨Y, h3, t3, hy, huy, hst3, hok3, hs3⟩
  · simp [isVal] at hbad
  obtain ⟨he3, rfl⟩ := beta_inv (by rfl) hst3
  subst he3
  have hoy := over_ext (over_trunc hoq (Nat.le_succ (N + 2))) hy
  -- the read, which returns the value that was planted
  rcases hs3 with ⟨hbad, -⟩ | ⟨X, h4, t4, hx, hux, hst4, hok4, hs4⟩
  · simp [isVal, subst] at hbad
  obtain ⟨he4, hread⟩ := read_step_inv hst4
  subst he4
  have hrb : ((hp.set (cellB G b) w).set (cellA G a) (canon G c))[cellB G b]? = some w := by
    rw [List.getElem?_set_ne (cellA_ne_cellB G haOp)]
    have hb : cellB G b < hp.length := by
      obtain ⟨u, hu', -⟩ := hhV.2 (cellB G b) _ hlB
      exact (List.getElem?_eq_some_iff.mp hu').1
    simp [hb]
  rw [hrb] at hread
  cases hread
  have hox := over_ext (over_trunc hoy (Nat.le_succ (N + 1))) hx
  exact hneg (N + 1) (by omega) X _ hox hux hok4 (safe_value_mem hwval hs4)

theorem probe_escapes_clause {m : Nat} (G : Graph (Fin m)) (hwf : WF G)
    {a b : List (Fin m)} (haOp : a ∈ opSets G) (hbOp : b ∈ opSets G) (j : Fin m)
    (h : ∀ c d, G j = Node.arr c d → c ≠ [] ∧ (Sep G c a ∨ Sep G b d)) :
    ∃ N, ∀ n, N ≤ n → ∀ (U : WorldT n) (hp : Heap),
      Over G n U → WorldAdm U → HeapOk n U hp →
        ¬ denote G j n U (probe (cellA G a) (cellB G b)) := by
  cases hG : G j with
  | nul =>
    exact ⟨0, fun n _ U _ _ _ _ hd => by
      obtain ⟨c, d, he⟩ := denote_lam_shape G hd; rw [hG] at he; exact absurd he (by simp)⟩
  | bool =>
    exact ⟨0, fun n _ U _ _ _ _ hd => by
      obtain ⟨c, d, he⟩ := denote_lam_shape G hd; rw [hG] at he; exact absurd he (by simp)⟩
  | ref e =>
    exact ⟨0, fun n _ U _ _ _ _ hd => by
      obtain ⟨c, d, he⟩ := denote_lam_shape G hd; rw [hG] at he; exact absurd he (by simp)⟩
  | arr c d =>
    obtain ⟨hcne, hor⟩ := h c d hG
    rcases hor with hsd | hsc
    · exact probe_escapes_dom G hG haOp hsd
    · exact probe_escapes_cod G hwf hG haOp hbOp hcne hsc

/-- **The arrow clause of covering is forced, when neither operand is empty.**
A source arrow whose domain no target clause contains, or whose codomain no
target clause covers, is separated from the target by one probe. -/
theorem sep_of_arr_unmatched {m : Nat} (G : Graph (Fin m)) (hwf : WF G)
    {S T : List (Fin m)} {i : Fin m} {a b : List (Fin m)} (hi : i ∈ S)
    (hG : G i = Node.arr a b) (hane : a ≠ []) (hbne : b ≠ [])
    (h : ∀ j ∈ T, ∀ c d, G j = Node.arr c d → c ≠ [] ∧ (Sep G c a ∨ Sep G b d)) :
    Sep G S T := by
  have haOp : a ∈ opSets G := opSets_dom hG hane
  have hbOp : b ∈ opSets G := opSets_cod hG hbne
  obtain ⟨N, hN⟩ := sep_of_clauses G (probe (cellA G a) (cellB G b)) T
    (fun j hj => probe_escapes_clause G hwf haOp hbOp j (h j hj))
  exact ⟨_, N, closed_probe _ _,
    fun n U ho => ⟨i, hi, probe_in_arrow G hG haOp hbOp n U ho⟩, hN⟩

/-! ### The degenerate arrows

Two shapes of source arrow have no probe, because a probe needs a cell at each
operand and an empty operand has none. They are separated by simpler values: an
arrow that cannot return is inhabited by a function that writes and then
diverges, and an arrow that is never applied is inhabited by a function that
would get stuck if it were. -/

theorem tester_in_arrow {m : Nat} (G : Graph (Fin m)) {i : Fin m} {a b : List (Fin m)}
    (hG : G i = Node.arr a b) (haOp : a ∈ opSets G) (n : Nat) (U : WorldT n)
    (ho : Over G n U) : denote G i n U (tester (cellA G a)) := by
  refine (denote_unfold G i n U _).mpr ?_
  unfold layer; rw [hG]
  exact tester_typed (denoteSet_adm G a) (denoteSet_valOnly G a) n U _
    ⟨_, _, rfl, WExt_lookup ho (graphWorld_lookup G n haOp), fun _ _ _ _ => Iff.rfl⟩

theorem tester_escapes_dom {m : Nat} (G : Graph (Fin m)) {a c d : List (Fin m)}
    {j : Fin m} (hG : G j = Node.arr c d) (haOp : a ∈ opSets G) (hs : Sep G c a) :
    ∃ N, ∀ n, N ≤ n → ∀ (U : WorldT n) (hp : Heap),
      Over G n U → WorldAdm U → HeapOk n U hp → ¬ denote G j n U (tester (cellA G a)) := by
  obtain ⟨v, N, -, hpos, hneg⟩ := hs
  have hval : isVal v = true := denoteSet_valOnly G c 0 _ v (hpos 0 _ (WExt_refl _))
  refine ⟨N + 4, ?_⟩
  intro n hN U h ho hu hh hv
  have ht := (denote_unfold G j n U _).mp hv
  unfold layer at ht; rw [hG] at ht
  have hoV : Over G (N + 3) (trunc (N + 3) (by omega) U) := over_trunc ho (by omega)
  have hhV : HeapOk (N + 3) (trunc (N + 3) (by omega) U) h := heap_down hh (N + 3) (by omega)
  have huV : WorldAdm (trunc (N + 3) (by omega) U) :=
    WorldAdm_trunc (show N + 3 ≤ n by omega) hu
  have hsafe := ht.2 (N + 3) (by omega) _ (WExt_refl _) huV h hhV v (hpos _ _ hoV)
  rcases hsafe with ⟨hbad, -⟩ | ⟨Z, h', tm, hz, -, hstep, -, hst⟩
  · simp [isVal] at hbad
  obtain ⟨he, rfl⟩ := tester_step_inv hval hstep
  subst he
  have hoz := over_ext (over_trunc hoV (Nat.le_succ (N + 2))) hz
  rcases hst with ⟨hbad, -⟩ | ⟨Q, h'', t', hq, huq, hs', hhq, -⟩
  · simp [isVal] at hbad
  obtain ⟨he2, -, hlt⟩ := write_step_inv hval hs'
  subst he2
  have hoq := over_ext (over_trunc hoz (Nat.le_succ (N + 1))) hq
  have hl := WExt_lookup hoq (graphWorld_lookup G (N + 1) haOp)
  obtain ⟨w, hw, hm⟩ := hhq.2 (cellA G a) (res (denoteSet G a)) hl
  simp [hlt] at hw
  subst hw
  exact hneg N (Nat.le_refl N) _ _ (over_trunc hoq (Nat.le_succ N))
    (WorldAdm_trunc (Nat.le_succ N) huq) (HeapOk_trunc N Q _ hhq)
    (hm N (show N < N + 1 by omega))

theorem sep_of_arr_empty_cod {m : Nat} (G : Graph (Fin m)) {S T : List (Fin m)}
    {i : Fin m} {a : List (Fin m)} (hi : i ∈ S) (hG : G i = Node.arr a [])
    (hane : a ≠ []) (h : ∀ j ∈ T, ∀ c d, G j = Node.arr c d → Sep G c a) : Sep G S T := by
  have haOp : a ∈ opSets G := opSets_dom hG hane
  obtain ⟨N, hN⟩ := sep_of_clauses G (tester (cellA G a)) T (fun j hj => by
    cases hG' : G j with
    | nul =>
      exact ⟨0, fun n _ U _ _ _ _ hd => by
        obtain ⟨c, d, he⟩ := denote_lam_shape G hd; rw [hG'] at he; exact absurd he (by simp)⟩
    | bool =>
      exact ⟨0, fun n _ U _ _ _ _ hd => by
        obtain ⟨c, d, he⟩ := denote_lam_shape G hd; rw [hG'] at he; exact absurd he (by simp)⟩
    | ref e =>
      exact ⟨0, fun n _ U _ _ _ _ hd => by
        obtain ⟨c, d, he⟩ := denote_lam_shape G hd; rw [hG'] at he; exact absurd he (by simp)⟩
    | arr c d => exact tester_escapes_dom G hG' haOp (h j hj c d hG'))
  exact ⟨_, N, closed_tester _, fun n U ho => ⟨i, hi, tester_in_arrow G hG haOp n U ho⟩, hN⟩

theorem stuck_in_arrow {m : Nat} (G : Graph (Fin m)) {i : Fin m} {b : List (Fin m)}
    (hG : G i = Node.arr [] b) (n : Nat) (U : WorldT n) : denote G i n U stuckFn := by
  refine (denote_unfold G i n U _).mpr ?_
  unfold layer; rw [hG]
  exact vacuous_arrow (fun j W v hv => by obtain ⟨k, hk, -⟩ := hv; simp at hk) _ n U

theorem stuck_escapes_clause {m : Nat} (G : Graph (Fin m)) (hwf : WF G) (j : Fin m)
    (h : ∀ c d, G j = Node.arr c d → c ≠ []) :
    ∃ N, ∀ n, N ≤ n → ∀ (U : WorldT n) (hp : Heap),
      Over G n U → WorldAdm U → HeapOk n U hp → ¬ denote G j n U stuckFn := by
  cases hG : G j with
  | nul =>
    exact ⟨0, fun n _ U _ _ _ _ hd => by
      obtain ⟨c, d, he⟩ := denote_lam_shape G hd; rw [hG] at he; exact absurd he (by simp)⟩
  | bool =>
    exact ⟨0, fun n _ U _ _ _ _ hd => by
      obtain ⟨c, d, he⟩ := denote_lam_shape G hd; rw [hG] at he; exact absurd he (by simp)⟩
  | ref e =>
    exact ⟨0, fun n _ U _ _ _ _ hd => by
      obtain ⟨c, d, he⟩ := denote_lam_shape G hd; rw [hG] at he; exact absurd he (by simp)⟩
  | arr c d =>
    have hcne := h c d hG
    refine ⟨3, ?_⟩
    intro n hN U hp ho hu hh hv
    have ht := (denote_unfold G j n U _).mp hv
    unfold layer at ht; rw [hG] at ht
    have hoV : Over G 2 (trunc 2 (by omega) U) := over_trunc ho (by omega)
    have huV : WorldAdm (trunc 2 (by omega) U) := WorldAdm_trunc (show 2 ≤ n by omega) hu
    have hhV : HeapOk 2 (trunc 2 (by omega) U) hp := heap_down hh 2 (by omega)
    have harg := canon_over G hwf c hcne 2 _ hoV
    have hsafe := ht.2 2 (by omega) _ (WExt_refl _) huV hp hhV (canon G c) harg
    rcases hsafe with ⟨hbad, -⟩ | ⟨Z, h1, t1, hz, huz, hst1, hok1, hs1⟩
    · simp [isVal] at hbad
    obtain ⟨he1, rfl⟩ := beta_inv (denoteSet_valOnly G c 2 _ _ harg) hst1
    subst he1
    exact stuck_not_safe _ 0 Z _ hs1

theorem sep_of_arr_empty_dom {m : Nat} (G : Graph (Fin m)) (hwf : WF G) {S T : List (Fin m)}
    {i : Fin m} {b : List (Fin m)} (hi : i ∈ S) (hG : G i = Node.arr [] b)
    (h : ∀ j ∈ T, ∀ c d, G j = Node.arr c d → c ≠ []) : Sep G S T := by
  obtain ⟨N, hN⟩ := sep_of_clauses G stuckFn T (fun j hj => stuck_escapes_clause G hwf j (h j hj))
  exact ⟨_, N, closed_stuck, fun n U _ => ⟨i, hi, stuck_in_arrow G hG n U⟩, hN⟩

/-! ### Completeness

Every clause of the source is now observable: an atom by its own value, a
reference by the canonical location of its operand, an arrow by a probe. So the
relation "not separated" is a covering relation, and a type included in another
is covered by it. With `sim_sound` this closes the loop: for the fragment this
file describes, the syntactic rule and the semantic inclusion are the same
thing. -/

def NotSep {m : Nat} (G : Graph (Fin m)) (S T : List (Fin m)) : Prop := ¬ Sep G S T

theorem notSep_simRel {m : Nat} (G : Graph (Fin m)) (hwf : WF G) :
    SimRel G (NotSep G) := by
  intro S T hST
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hS
    refine Classical.byContradiction (fun hT => ?_)
    exact hST (sep_nul G hS hT)
  · intro hS
    refine Classical.byContradiction (fun hT => ?_)
    exact hST (sep_bool G hS hT)
  · intro a ha
    refine Classical.byContradiction (fun hno => ?_)
    refine hST (sep_of_ref_unmatched G hwf ha (fun b hb => ?_))
    by_cases h1 : Sep G a b
    · exact sep_famDiff G hwf h1
    · by_cases h2 : Sep G b a
      · exact famDiff_symm G (sep_famDiff G hwf h2)
      · exact absurd ⟨b, hb, h1, h2⟩ hno
  · intro a b hab
    refine Classical.byContradiction (fun hno => ?_)
    have key : ∀ j ∈ T, ∀ c d, G j = Node.arr c d →
        c ≠ [] ∧ (Sep G c a ∨ (b ≠ [] ∧ Sep G b d)) := by
      intro j hj c d hGj
      have hcd : (c, d) ∈ arrOps G T := mem_arrOps hj hGj
      refine ⟨fun hce => hno ⟨c, d, hcd, Or.inl hce⟩, ?_⟩
      by_cases h1 : Sep G c a
      · exact Or.inl h1
      · by_cases h2 : b = []
        · exact absurd ⟨c, d, hcd, Or.inr ⟨h1, Or.inl h2⟩⟩ hno
        · by_cases h3 : Sep G b d
          · exact Or.inr ⟨h2, h3⟩
          · exact absurd ⟨c, d, hcd, Or.inr ⟨h1, Or.inr h3⟩⟩ hno
    obtain ⟨i, hi, hGi⟩ := arrOps_mem hab
    refine hST ?_
    by_cases hane : a = []
    · subst hane
      exact sep_of_arr_empty_dom G hwf hi hGi (fun j hj c d hGj => (key j hj c d hGj).1)
    · by_cases hbne : b = []
      · subst hbne
        refine sep_of_arr_empty_cod G hi hGi hane (fun j hj c d hGj => ?_)
        rcases (key j hj c d hGj).2 with h | ⟨hb, -⟩
        · exact h
        · exact absurd rfl hb
      · refine sep_of_arr_unmatched G hwf hi hGi hane hbne (fun j hj c d hGj => ?_)
        refine ⟨(key j hj c d hGj).1, ?_⟩
        rcases (key j hj c d hGj).2 with h | ⟨-, h⟩
        · exact Or.inl h
        · exact Or.inr h

/-- **Covering is complete.** In a well-formed graph, one type is included in
another exactly when a covering certificate says so. The inclusion needs to hold
only at the canonical worlds; `sim_sound` gives it back at every world. -/
theorem sim_iff_incl {m : Nat} (G : Graph (Fin m)) (hwf : WF G) (S T : List (Fin m)) :
    Sim G S T ↔
      ∀ (n : Nat) (v : Val),
        denoteSet G S n (graphWorld G n) v → denoteSet G T n (graphWorld G n) v := by
  constructor
  · intro hsim n v hv
    exact Sim_sound G hsim n _ v hv
  · intro hincl
    refine ⟨NotSep G, notSep_simRel G hwf, fun hs => ?_⟩
    obtain ⟨v, N, -, hpos, hneg⟩ := hs
    exact hneg N (Nat.le_refl N) _ (graphHeap G) (WExt_refl _) (graphWorld_adm G N)
      (graphHeap_ok G hwf N) (hincl N v (hpos N _ (WExt_refl _)))

/-! ### One clause lands in one clause

The practical form of the result. A source type with a single clause that is
included in a union is included in *one member* of that union — single clauses
are union-prime. This is what lets a checker match one clause at a time instead
of reasoning about the union as a whole, and it is exactly what fails in a pure
language, where a function into `nul ∨ bool` lies in the union of the two arrow
types without lying in either. -/

theorem Cover_mono {ι : Type} (G : Graph ι) {R R' : List ι → List ι → Prop}
    (h : ∀ S T, R S T → R' S T) {S T : List ι} (hc : Cover G R S T) : Cover G R' S T := by
  refine ⟨hc.1, hc.2.1, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, hab, hba⟩ := hc.2.2.1 a ha
    exact ⟨b, hb, h _ _ hab, h _ _ hba⟩
  · intro a b hab
    obtain ⟨c, d, hcd, hor⟩ := hc.2.2.2 a b hab
    refine ⟨c, d, hcd, ?_⟩
    rcases hor with hce | ⟨hca, hbd⟩
    · exact Or.inl hce
    · exact Or.inr ⟨h _ _ hca, hbd.imp id (h _ _)⟩

theorem hasNul_singleton {ι : Type} {G : Graph ι} {i : ι} (h : hasNul G [i]) : G i = Node.nul := by
  obtain ⟨k, hk, hG⟩ := h
  rwa [List.mem_singleton.mp hk] at hG

theorem hasBool_singleton {ι : Type} {G : Graph ι} {i : ι} (h : hasBool G [i]) :
    G i = Node.bool := by
  obtain ⟨k, hk, hG⟩ := h
  rwa [List.mem_singleton.mp hk] at hG

theorem refOps_singleton {ι : Type} {G : Graph ι} {i : ι} {a : List ι}
    (h : a ∈ refOps G [i]) : G i = Node.ref a := by
  obtain ⟨k, hk, hG⟩ := refOps_mem h
  rwa [List.mem_singleton.mp hk] at hG

theorem arrOps_singleton {ι : Type} {G : Graph ι} {i : ι} {a b : List ι}
    (h : (a, b) ∈ arrOps G [i]) : G i = Node.arr a b := by
  obtain ⟨k, hk, hG⟩ := arrOps_mem h
  rwa [List.mem_singleton.mp hk] at hG

/-- **Single clauses are union-prime.** -/
theorem sim_clause_prime {m : Nat} (G : Graph (Fin m)) {i : Fin m} {T : List (Fin m)}
    (h : Sim G [i] T) : ∃ j ∈ T, Sim G [i] [j] := by
  obtain ⟨R, hR, hiT⟩ := h
  have hc := hR _ _ hiT
  cases hG : G i with
  | nul =>
    obtain ⟨j, hj, hGj⟩ := hc.1 ⟨i, by simp, hG⟩
    refine ⟨j, hj, fun S T => S = [i] ∧ T = [j], ?_, rfl, rfl⟩
    rintro S T ⟨rfl, rfl⟩
    refine ⟨fun _ => ⟨j, by simp, hGj⟩, ?_, ?_, ?_⟩
    · intro hb; rw [hasBool_singleton hb] at hG; exact absurd hG (by simp)
    · intro a ha; rw [refOps_singleton ha] at hG; exact absurd hG (by simp)
    · intro a b hab; rw [arrOps_singleton hab] at hG; exact absurd hG (by simp)
  | bool =>
    obtain ⟨j, hj, hGj⟩ := hc.2.1 ⟨i, by simp, hG⟩
    refine ⟨j, hj, fun S T => S = [i] ∧ T = [j], ?_, rfl, rfl⟩
    rintro S T ⟨rfl, rfl⟩
    refine ⟨?_, fun _ => ⟨j, by simp, hGj⟩, ?_, ?_⟩
    · intro hb; rw [hasNul_singleton hb] at hG; exact absurd hG (by simp)
    · intro a ha; rw [refOps_singleton ha] at hG; exact absurd hG (by simp)
    · intro a b hab; rw [arrOps_singleton hab] at hG; exact absurd hG (by simp)
  | ref a =>
    obtain ⟨b, hb, hab, hba⟩ := hc.2.2.1 a (mem_refOps (by simp) hG)
    obtain ⟨j, hj, hGj⟩ := refOps_mem hb
    refine ⟨j, hj, fun S T => (S = [i] ∧ T = [j]) ∨ R S T, ?_, Or.inl ⟨rfl, rfl⟩⟩
    rintro S T (⟨rfl, rfl⟩ | hRST)
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro hn; rw [hasNul_singleton hn] at hG; exact absurd hG (by simp)
      · intro hbo; rw [hasBool_singleton hbo] at hG; exact absurd hG (by simp)
      · intro a' ha'
        have he : a' = a := by
          have hr := refOps_singleton ha'
          rw [hG] at hr
          simpa [Node.ref.injEq] using hr.symm
        subst he
        exact ⟨b, mem_refOps (by simp) hGj, Or.inr hab, Or.inr hba⟩
      · intro a' b' hab'; rw [arrOps_singleton hab'] at hG; exact absurd hG (by simp)
    · exact Cover_mono G (fun _ _ hx => Or.inr hx) (hR _ _ hRST)
  | arr a b =>
    obtain ⟨c, d, hcd, hor⟩ := hc.2.2.2 a b (mem_arrOps (by simp) hG)
    obtain ⟨j, hj, hGj⟩ := arrOps_mem hcd
    refine ⟨j, hj, fun S T => (S = [i] ∧ T = [j]) ∨ R S T, ?_, Or.inl ⟨rfl, rfl⟩⟩
    rintro S T (⟨rfl, rfl⟩ | hRST)
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro hn; rw [hasNul_singleton hn] at hG; exact absurd hG (by simp)
      · intro hbo; rw [hasBool_singleton hbo] at hG; exact absurd hG (by simp)
      · intro a' ha'; rw [refOps_singleton ha'] at hG; exact absurd hG (by simp)
      · intro a' b' hab'
        have he := arrOps_singleton hab'
        rw [hG] at he
        obtain ⟨rfl, rfl⟩ : a = a' ∧ b = b' := by
          simpa [Node.arr.injEq] using he
        refine ⟨c, d, mem_arrOps (by simp) hGj, ?_⟩
        rcases hor with hce | ⟨hca, hbd⟩
        · exact Or.inl hce
        · exact Or.inr ⟨Or.inr hca, hbd.imp id Or.inr⟩
    · exact Cover_mono G (fun _ _ hx => Or.inr hx) (hR _ _ hRST)

/-- The semantic reading of primality: a single-clause type included in a union
is included in one of its clauses. -/
theorem incl_clause_prime {m : Nat} (G : Graph (Fin m)) (hwf : WF G) (i : Fin m)
    (T : List (Fin m))
    (h : ∀ (n : Nat) (v : Val),
      denoteSet G [i] n (graphWorld G n) v → denoteSet G T n (graphWorld G n) v) :
    ∃ j ∈ T, ∀ (n : Nat) (v : Val),
      denoteSet G [i] n (graphWorld G n) v → denoteSet G [j] n (graphWorld G n) v := by
  obtain ⟨j, hj, hsim⟩ := sim_clause_prime G ((sim_iff_incl G hwf [i] T).mpr h)
  exact ⟨j, hj, (sim_iff_incl G hwf [i] [j]).mp hsim⟩

/-- **The shape of the check.** One type is below another exactly when every
clause of the source is below a *single* clause of the target. The left-to-right
direction is primality; the right-to-left one is that a union on the left is
handled clause by clause. Together they say a checker never has to reason about
a union as a whole. -/
theorem sim_pairwise {m : Nat} (G : Graph (Fin m)) (hwf : WF G) (S T : List (Fin m)) :
    Sim G S T ↔ ∀ i ∈ S, ∃ j ∈ T, Sim G [i] [j] := by
  constructor
  · intro hsim i hi
    have hincl := (sim_iff_incl G hwf S T).mp hsim
    refine sim_clause_prime G ((sim_iff_incl G hwf [i] T).mpr (fun n v hv => ?_))
    obtain ⟨k, hk, hd⟩ := hv
    exact hincl n v ⟨k, by rw [List.mem_singleton.mp hk]; exact hi, hd⟩
  · intro h
    refine (sim_iff_incl G hwf S T).mpr (fun n v hv => ?_)
    obtain ⟨i, hi, hd⟩ := hv
    obtain ⟨j, hj, hsim⟩ := h i hi
    obtain ⟨k, hk, hd'⟩ := (sim_iff_incl G hwf [i] [j]).mp hsim n v ⟨i, by simp, hd⟩
    exact ⟨k, by rw [List.mem_singleton.mp hk]; exact hj, hd'⟩

/-! ### The empty domain, and why covering needs a case for it

`never → bool` accepts every lambda, so `null → null` lies below it whatever the
two result types are. A rule that compared results would reject this, which is
why `Cover` carries the extra disjunct. -/

def emptyG : Graph (Fin 4) := fun i =>
  match i.val with
  | 0 => .nul
  | 1 => .bool
  | 2 => .arr [0] [0]
  | _ => .arr [] [1]

theorem arr_empty_dom_incl : ∀ (n : Nat) (W : WorldT n) (v : Val),
    denoteSet emptyG [2] n W v → denoteSet emptyG [3] n W v := by
  rintro n W v ⟨i, hi, hd⟩
  simp only [List.mem_singleton] at hi
  subst hi
  obtain ⟨hlam, -⟩ := (denote_unfold emptyG 2 n W v).mp hd
  refine ⟨3, by simp, (denote_unfold emptyG 3 n W v).mpr ⟨hlam, ?_⟩⟩
  rintro m _ W' _ _ _ _ x ⟨k, hk, -⟩
  simp at hk

theorem arr_empty_dom : Sim emptyG [2] [3] := by
  refine ⟨fun S T => S = [2] ∧ T = [3], ?_, rfl, rfl⟩
  rintro S T ⟨rfl, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨i, hi, hG⟩
    simp only [List.mem_singleton] at hi
    subst hi
    rw [show emptyG 2 = Node.arr [0] [0] from rfl] at hG
    simp at hG
  · rintro ⟨i, hi, hG⟩
    simp only [List.mem_singleton] at hi
    subst hi
    rw [show emptyG 2 = Node.arr [0] [0] from rfl] at hG
    simp at hG
  · intro a ha
    rw [show refOps emptyG [2] = [] from rfl] at ha
    simp at ha
  · intro a b _
    exact ⟨[], [1], mem_arrOps (i := 3) (by simp) rfl, Or.inl rfl⟩

/-! ### What the restriction excludes

Four shapes make an arrow's obligation vanish, and every one of them needs a cell
that can hold nothing. `ref never` as a **domain**: no argument can be supplied.
`ref never` as a **result**: the function can only diverge, and divergence is safe
at any result type. A domain only *partly* unreachable, where the survivors are
what should have been compared. And one level up, `ref (ref never)`, invisible
because an arrow demands nothing below budget two.

All four are ill-formed, which is what `WF` is for — and why the covering rule
needs no per-clause vacuity analysis. -/

def excluded : Graph (Fin 7) := fun i =>
  match i.val with
  | 0 => .nul
  | 1 => .bool
  | 2 => .ref []            -- a cell that can hold nothing
  | 3 => .ref [2]           -- and one level up
  | 4 => .arr [2] [1]       -- (ref never) → bool: nothing can be supplied
  | 5 => .arr [0] [2]       -- null → (ref never): can only diverge
  | _ => .arr [2, 0] [0]    -- ((ref never) ∨ null) → null: partly unreachable

theorem excluded_not_wf : ¬ WF excluded := fun h => h 2 rfl

/-! ## What the generalisation buys

`ref (A ∨ B)` and `ref A ∨ ref B` are different types, and with operands
restricted to single nodes only the second is expressible. Both are expressible
here, and they are separated by a location whose declared contract is the
union: it inhabits the first and, references being invariant, neither clause of
the second. -/

def exG : Graph (Fin 5) := fun i =>
  match i.val with
  | 0 => .nul
  | 1 => .bool
  | 2 => .ref [0]
  | 3 => .ref [1]
  | _ => .ref [0, 1]

/-- The world declares one cell to hold `null ∨ bool`. -/
def exW (n : Nat) : WorldT n := ofList [res (denoteSet exG [0, 1])]

theorem exG_bool_tru (n : Nat) (W : WorldT n) : denote exG 1 n W .tru :=
  (denote_unfold exG 1 n W _).mpr (Or.inl rfl)

theorem loc_in_ref_union (n : Nat) : denoteSet exG [4] n (exW n) (.loc 0) := by
  refine ⟨4, by simp, (denote_unfold exG 4 n _ _).mpr ?_⟩
  exact ⟨0, res (denoteSet exG [0, 1]), rfl, by simp [lookup, exW], fun _ _ _ _ => Iff.rfl⟩

theorem exG_nul_nul (n : Nat) (W : WorldT n) : denote exG 0 n W .nul :=
  (denote_unfold exG 0 n W _).mpr rfl

theorem loc_not_in_union_ref : ¬ denoteSet exG [2, 3] 1 (exW 1) (.loc 0) := by
  rintro ⟨i, hi, hd⟩
  have hd' := (denote_unfold exG i 1 _ _).mp hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · -- the cell would have to be a `ref null`, but it may hold `true`
    obtain ⟨l, c, hv, hl, hag⟩ := hd'
    cases hv
    simp only [lookup, exW, toList_ofList, List.getElem?_cons_zero,
      Option.some.injEq] at hl
    subst hl
    obtain ⟨j, hj, hjd⟩ :=
      (hag 0 (by omega) (ofList []) .tru).mp ⟨1, by simp, exG_bool_tru 0 _⟩
    simp only [List.mem_singleton] at hj
    subst hj
    exact absurd ((denote_unfold exG 0 0 _ _).mp hjd)
      (by simp [layer, exG, nodeSem, nulT])
  · -- or a `ref bool`, but it may hold `null`
    obtain ⟨l, c, hv, hl, hag⟩ := hd'
    cases hv
    simp only [lookup, exW, toList_ofList, List.getElem?_cons_zero,
      Option.some.injEq] at hl
    subst hl
    obtain ⟨j, hj, hjd⟩ :=
      (hag 0 (by omega) (ofList []) .nul).mp ⟨0, by simp, exG_nul_nul 0 _⟩
    simp only [List.mem_singleton] at hj
    subst hj
    exact absurd ((denote_unfold exG 1 0 _ _).mp hjd)
      (by simp [layer, exG, nodeSem, boolT])

/-- **Both sides are expressible, and they differ.** -/
theorem ref_union_ne_union_ref :
    ¬ (∀ (n : Nat) (W : WorldT n) (v : Val),
        denoteSet exG [4] n W v ↔ denoteSet exG [2, 3] n W v) :=
  fun h => loc_not_in_union_ref ((h 1 (exW 1) (.loc 0)).mp (loc_in_ref_union 1))

end Union
end ExperimentState
end Verification
