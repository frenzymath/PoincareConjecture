import PoincareConjecture.Definitions.Ch11.BlowupLimits








set_option autoImplicit false

open scoped ENNReal

namespace PoincareConjecture.M30


@[simp] theorem blowupBackwardInterval_top :
    blowupBackwardInterval ⊤ = Set.Iic 0 := by
  ext t
  simp [blowupBackwardInterval]



@[simp] theorem zero_mem_blowupBackwardInterval {T : ℝ≥0∞} :
    0 ∈ blowupBackwardInterval T ↔ 0 < T := by
  simp [blowupBackwardInterval]



theorem blowupBackwardInterval_mono {T T' : ℝ≥0∞} (h : T ≤ T') :
    blowupBackwardInterval T ⊆ blowupBackwardInterval T' := by
  intro t ht
  exact ⟨ht.1, ht.2.trans_le h⟩



theorem blowupBackwardInterval_ofReal {T : ℝ} (hT : 0 < T) :
    blowupBackwardInterval (ENNReal.ofReal T) = Set.Ioc (-T) 0 := by
  ext t
  simp only [blowupBackwardInterval, Set.mem_ofPred_eq, Set.mem_Ioc,
    ENNReal.ofReal_lt_ofReal_iff hT]
  constructor
  · rintro ⟨ht, h⟩
    exact ⟨neg_lt.mp h, ht⟩
  · rintro ⟨h, ht⟩
    exact ⟨ht, neg_lt.mpr h⟩



theorem closedSlab_subset_blowupBackwardInterval {T : ℝ} {T₀ : ℝ≥0∞}
    (hT : ENNReal.ofReal T < T₀) :
    Set.Icc (-T) 0 ⊆ blowupBackwardInterval T₀ := by
  intro t ht
  exact ⟨ht.2, (ENNReal.ofReal_le_ofReal (neg_le.mp ht.1)).trans_lt hT⟩

end PoincareConjecture.M30
