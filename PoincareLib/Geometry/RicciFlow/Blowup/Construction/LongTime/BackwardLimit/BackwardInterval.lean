import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Geometry

/-!
# The backward interval of Theorem 11.8

Morgan--Tian Theorem 11.8, p. 272, includes its terminal time and excludes its
finite left endpoint. An infinite horizon gives the full ancient interval.
-/

set_option autoImplicit false

open scoped ENNReal

namespace PoincareMT.M30

/-- An infinite horizon is exactly the ancient domain (Theorem 11.8, p. 272). -/
@[simp] theorem blowupBackwardInterval_top :
    blowupBackwardInterval ⊤ = Set.Iic 0 := by
  ext t
  simp [blowupBackwardInterval]

/-- The terminal time is included precisely for a positive horizon
(Theorem 11.8, p. 272). -/
@[simp] theorem zero_mem_blowupBackwardInterval {T : ℝ≥0∞} :
    0 ∈ blowupBackwardInterval T ↔ 0 < T := by
  simp [blowupBackwardInterval]

/-- Increasing the horizon increases the backward domain
(Theorem 11.8, p. 272). -/
theorem blowupBackwardInterval_mono {T T' : ℝ≥0∞} (h : T ≤ T') :
    blowupBackwardInterval T ⊆ blowupBackwardInterval T' := by
  intro t ht
  exact ⟨ht.1, ht.2.trans_le h⟩

/-- A positive finite horizon gives the expected half-open real interval
(Theorem 11.8, p. 272). -/
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

/-- Every closed slab strictly below the horizon lies in the limit domain
(Theorem 11.8, p. 272; Definition 5.12, p. 90). -/
theorem closedSlab_subset_blowupBackwardInterval {T : ℝ} {T₀ : ℝ≥0∞}
    (hT : ENNReal.ofReal T < T₀) :
    Set.Icc (-T) 0 ⊆ blowupBackwardInterval T₀ := by
  intro t ht
  exact ⟨ht.2, (ENNReal.ofReal_le_ofReal (neg_le.mp ht.1)).trans_lt hT⟩

end PoincareMT.M30
