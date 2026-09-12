import Verification.ExperimentState.HeapFacts

namespace Verification.ExperimentState.HeapFactsTests
open HeapFacts

-- Widen contents, preserve identity, retain aliases through repeated maps.
#guard check [⟨2,[.tru]⟩] [⟨0,[.tru,.fls]⟩,⟨1,[.tru]⟩] (some [2,2])
#guard !check [⟨2,[.tru,.fls]⟩] [⟨0,[.tru]⟩] (some [2])
#guard !check [⟨2,[.tru]⟩] [⟨0,[.tru]⟩] (some [1])
#guard !check [] [⟨0,[.tru]⟩] none
#guard check [⟨0,[.tru]⟩] [] none

-- Two variables naming the same location cannot satisfy contradictory facts.
theorem aliases_agree {ρ h i j} (he : ρ i = ρ j)
    (hf : Holds [⟨i,[.tru]⟩,⟨j,[.fls]⟩] ρ h) : False := by
  obtain ⟨l,c,v,hl,hv,a,ha,rfl⟩ := hf ⟨i,[.tru]⟩ (by simp)
  obtain ⟨k,d,u,hk,hu,b,hb,rfl⟩ := hf ⟨j,[.fls]⟩ (by simp)
  simp only [List.mem_singleton] at ha hb
  subst a; subst b
  have heq : l = k := by
    have ho : Tm.obj l c = .obj k d := hl.symm.trans (he.trans hk)
    exact (Tm.obj.inj ho).1
  subst k
  have := hv.symm.trans hu
  cases this

#print axioms aliases_agree
end Verification.ExperimentState.HeapFactsTests
