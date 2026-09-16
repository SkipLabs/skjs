import Verification.ExperimentState.HeapFacts

namespace Verification.ExperimentState.HeapFactsTests
open HeapFacts

-- Widen contents, preserve identity, retain aliases through repeated maps.
#guard check [⟨2,[.tru],valueField⟩] [⟨0,[.tru,.fls],valueField⟩,⟨1,[.tru],valueField⟩] (some [2,2])
#guard !check [⟨2,[.tru,.fls],valueField⟩] [⟨0,[.tru],valueField⟩] (some [2])
#guard !check [⟨2,[.tru],valueField⟩] [⟨0,[.tru],valueField⟩] (some [1])
#guard !check [] [⟨0,[.tru],valueField⟩] none
#guard check [⟨0,[.tru],valueField⟩] [] none

-- Two variables naming the same location cannot satisfy contradictory facts.
theorem aliases_agree {ρ h i j} (he : ρ i = ρ j)
    (hf : Holds [⟨i,[.tru],valueField⟩,⟨j,[.fls],valueField⟩] ρ h) : False := by
  obtain ⟨flds,c,l,v,hl,hfd,hv,a,ha,rfl⟩ := hf ⟨i,[.tru],valueField⟩ (by simp)
  obtain ⟨flds',d,k,u,hk,hfd',hu,b,hb,rfl⟩ := hf ⟨j,[.fls],valueField⟩ (by simp)
  simp only [List.mem_singleton] at ha hb
  subst a; subst b
  have heq : l = k := by
    have ho : Tm.objAt flds c = .objAt flds' d := hl.symm.trans (he.trans hk)
    cases ho
    exact Option.some.inj (hfd.symm.trans hfd')
  subst k
  have := hv.symm.trans hu
  cases this

#print axioms aliases_agree
end Verification.ExperimentState.HeapFactsTests
