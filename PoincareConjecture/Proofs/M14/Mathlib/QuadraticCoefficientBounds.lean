import PoincareConjecture.Proofs.M14.Mathlib.CompactSpatialJets










set_option autoImplicit false

set_option synthInstance.maxSize 2048

open Set Filter
open scoped ContDiff NNReal Topology

namespace PoincareConjecture.M14

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]




theorem exists_quadratic_coefficient_bounds {a b : ℝ} (hab : a < b)
    {U S : Set E} (hU : IsOpen U) (hS : IsCompact S) (hconvex : Convex ℝ S) (hsub : S ⊆ U)
    (B : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (V : ℝ × E → ℝ)
    (hB : ContDiffOn ℝ ∞ B (Icc a b ×ˢ U)) (hV : ContDiffOn ℝ ∞ V (Icc a b ×ˢ U))
    (hpos : ∀ z ∈ Icc a b ×ˢ U, ∀ v : E, v ≠ 0 → 0 < B z v v) :
    ∃ m : ℝ, 0 < m ∧ ∃ K : ℝ≥0,
      (∀ z ∈ Icc a b ×ˢ S, ∀ v : E, m * ‖v‖ ^ 2 ≤ B z v v) ∧
      ∀ s ∈ Icc a b,
        LipschitzOnWith K (fun z => B (s, z)) S ∧
        LipschitzOnWith K (fun z => M08.spatialWithinFDeriv (Icc a b) U B (s, z)) S ∧
        LipschitzOnWith K (fun z => M08.spatialWithinFDeriv (Icc a b) U V (s, z)) S := by
  have hsmall : Icc a b ×ˢ S ⊆ Icc a b ×ˢ U := prod_mono_right hsub
  obtain ⟨m, hm, hcoercive⟩ := M08.compact_positive_forms_coercive
    (isCompact_Icc.prod hS) B (hB.continuousOn.mono hsmall)
    (fun z hz => hpos z (hsmall hz))
  have hDB := M08.spatialWithinFDeriv_contDiffOn (uniqueDiffOn_Icc hab) hU B hB
  have hDV := M08.spatialWithinFDeriv_contDiffOn (uniqueDiffOn_Icc hab) hU V hV
  obtain ⟨K₀, hK₀⟩ := compact_spatial_lipschitz_within hab hU hS hconvex hsub B hB
  obtain ⟨K₁, hK₁⟩ := compact_spatial_lipschitz_within hab hU hS hconvex hsub _ hDB
  obtain ⟨K₂, hK₂⟩ := compact_spatial_lipschitz_within hab hU hS hconvex hsub _ hDV
  refine ⟨m, hm, K₀ + K₁ + K₂, hcoercive, ?_⟩
  intro s hs
  refine ⟨(hK₀ s hs).weaken ?_, (hK₁ s hs).weaken ?_, (hK₂ s hs).weaken ?_⟩
  · exact (le_add_of_nonneg_right (show 0 ≤ K₁ from zero_le)).trans
      (le_add_of_nonneg_right (show 0 ≤ K₂ from zero_le))
  · exact (le_add_of_nonneg_left (show 0 ≤ K₀ from zero_le)).trans
      (le_add_of_nonneg_right (show 0 ≤ K₂ from zero_le))
  · exact le_add_of_nonneg_left (show 0 ≤ K₀ + K₁ from zero_le)




theorem exists_short_quadratic_interval {m β η : ℝ} (hm : 0 < m) (hη : 0 < η) :
    ∃ d : ℝ, 0 < d ∧ d ≤ η ∧ ∀ b ∈ Ioc (0 : ℝ) d, 0 < m / 4 - β * b ^ 2 := by
  have hc : ContinuousAt (fun b : ℝ => m / 4 - β * b ^ 2) 0 := by fun_prop
  have hpos : 0 < m / 4 - β * (0 : ℝ) ^ 2 := by simpa using div_pos hm (by norm_num : (0 : ℝ) < 4)
  have hevent : ∀ᶠ b in 𝓝 (0 : ℝ), 0 < m / 4 - β * b ^ 2 := hc.eventually (Ioi_mem_nhds hpos)
  obtain ⟨ε, hε, hbound⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨min η (ε / 2), lt_min hη (half_pos hε), min_le_left _ _, ?_⟩
  intro b hb
  apply hbound
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hb.1]
  exact (hb.2.trans (min_le_right _ _)).trans_lt (half_lt_self hε)

end PoincareConjecture.M14
