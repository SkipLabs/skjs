import Verification.Model.Types.PositiveNormalization

/-! Normalize each body of a guarded recursive graph without unfolding cycles
or allocating new labels. A label names a whole positive formula; normalized
labels name finite unions of clauses. Operands remain lists of labels. -/
namespace Verification.Model.PositiveGraphs
open PositiveNormalization Tower

abbrev Graph (ι : Type) := ι → Formula (List ι)
abbrev NormalGraph (ι : Type) := ι → List (Clause (List ι))

def normalizeGraph (G : Graph ι) : NormalGraph ι := fun i => normalize (G i)

def layer (G : Graph ι) (X : ι → Fam) (i : ι) : Fam := eval (setSem X) (G i)
def normalLayer (G : NormalGraph ι) (X : ι → Fam) (i : ι) : Fam := semList (setSem X) (G i)

theorem eval_congr (X Y : α → Fam) (n : Nat) (h : ∀ a, Agree (X a) (Y a) n)
    (f : Formula α) (W : WorldT n) (v : Val) : eval X f n W v ↔ eval Y f n W v := by
  induction f with
  | bot => rfl
  | atom c => exact sem_congr X Y n h c W v
  | union a b ih ih' => exact or_congr ih ih'
  | inter a b ih ih' => exact and_congr ih ih'

theorem eval_adm (X : α → Fam) (f : Formula α) : Adm (eval X f) := by
  induction f with
  | bot => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | atom c => exact sem_adm X c
  | union a b ih ih' => exact unionT_adm _ _ ih ih'
  | inter a b ih ih' => exact interT_adm _ _ ih ih'

theorem layer_congr (G : Graph ι) : LayerCongr (layer G) := by
  intro X Y n h i W v
  exact eval_congr _ _ n (fun a => setSem_congr n h a) (G i) W v

theorem layer_adm (G : Graph ι) : LayerAdm (layer G) := fun X _ i => eval_adm (setSem X) (G i)

/-- Equality of the entire guarded operators, not just an equation about one
nonrecursive example. -/
theorem normalized_layer (G : Graph ι) : normalLayer (normalizeGraph G) = layer G := by
  funext X i n W v
  exact propext (normalize_sound (setSem X) (G i) n W v)

def denote (G : Graph ι) : ι → Fam := Tower.denote (layer G)
def normalDenote (G : NormalGraph ι) : ι → Fam := Tower.denote (normalLayer G)

theorem normalize_recursive (G : Graph ι) : normalDenote (normalizeGraph G) = denote G := by
  unfold normalDenote denote
  rw [normalized_layer]

theorem unfolds (G : Graph ι) (i : ι) (n W v) :
    denote G i n W v ↔ layer G (denote G) i n W v :=
  Tower.denote_unfold (layer_congr G) i n W v

theorem admissible (G : Graph ι) (i : ι) : Adm (denote G i) :=
  Tower.denote_adm (layer_congr G) (layer_adm G) i

/-- Any sound check on normalized denotations transports to the original graph.
This is a normalization interface, not an assumption that the old subtype
checker already accepts the new reference-conjunction representation. -/
theorem transport_inclusion (G : Graph ι) (S T : List ι)
    (h : FamLe (setSem (normalDenote (normalizeGraph G)) S)
      (setSem (normalDenote (normalizeGraph G)) T)) :
    FamLe (setSem (denote G) S) (setSem (denote G) T) := by
  simpa only [normalize_recursive] using h

#print axioms normalize_recursive
#print axioms admissible
end Verification.Model.PositiveGraphs
