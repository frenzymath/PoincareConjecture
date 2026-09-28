import Mathlib.Analysis.ConstantSpeed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.EMetricSpace.VariationOnFromTo

open Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace Poincare.MetricCurves

variable {M : Type*} [MetricSpace M]

theorem continuousOn_cumulative_variation
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn γ (Icc a b)) (hv : BoundedVariationOn γ (Icc a b)) :
    ContinuousOn (variationOnFromTo γ (Icc a b) a) (Icc a b) := by
  intro t ht
  apply continuousWithinAt_iff_continuous_left'_right'.mpr
  constructor
  · simpa only [ContinuousWithinAt, dist_self, sub_zero] using
      variationOnFromTo.tendsto_left (left_mem_Icc.mpr hab) ht
        hv.locallyBoundedVariationOn ((hc t ht).mono inter_subset_left)
  · simpa only [ContinuousWithinAt, dist_self, add_zero] using
      variationOnFromTo.tendsto_right (left_mem_Icc.mpr hab) ht
        hv.locallyBoundedVariationOn ((hc t ht).mono inter_subset_left)

theorem exists_arcLength_representative
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn γ (Icc a b)) (hv : BoundedVariationOn γ (Icc a b)) :
    ∃ η : ℝ → M,
      η 0 = γ a ∧ η (eVariationOn γ (Icc a b)).toReal = γ b ∧
      η '' Icc 0 (eVariationOn γ (Icc a b)).toReal = γ '' Icc a b ∧
      HasUnitSpeedOn η (Icc 0 (eVariationOn γ (Icc a b)).toReal) ∧
      LipschitzOnWith 1 η (Icc 0 (eVariationOn γ (Icc a b)).toReal) := by
  let η := naturalParameterization γ (Icc a b) a
  let v := variationOnFromTo γ (Icc a b) a
  have hv0 : v a = 0 := variationOnFromTo.self _ _ _
  have hv1 : v b = (eVariationOn γ (Icc a b)).toReal := by
    simp only [v, variationOnFromTo.eq_of_le _ _ hab, inter_self]
  have himage : v '' Icc a b = Icc 0 (eVariationOn γ (Icc a b)).toReal := by
    rw [← hv0, ← hv1]
    exact (continuousOn_cumulative_variation hab hc hv).image_Icc_of_monotoneOn hab
      (variationOnFromTo.monotoneOn hv.locallyBoundedVariationOn (left_mem_Icc.mpr hab))
  have hread : ∀ t ∈ Icc a b, η (v t) = γ t := fun t ht =>
    edist_eq_zero.mp (edist_naturalParameterization_eq_zero hv.locallyBoundedVariationOn
      (left_mem_Icc.mpr hab) ht)
  have hunit : HasUnitSpeedOn η (Icc 0 (eVariationOn γ (Icc a b)).toReal) := by
    rw [← himage]
    exact has_unit_speed_naturalParameterization γ hv.locallyBoundedVariationOn
      (left_mem_Icc.mpr hab)
  refine ⟨η, ?_, ?_, ?_, hunit, ?_⟩
  · rw [← hv0]
    exact hread a (left_mem_Icc.mpr hab)
  · rw [← hv1]
    exact hread b (right_mem_Icc.mpr hab)
  · rw [← himage, image_image]
    exact image_congr hread
  · intro s hs t ht
    wlog hst : s ≤ t generalizing s t
    · simpa only [edist_comm] using this ht hs (le_of_not_ge hst)
    have hbound := eVariationOn.edist_le η
      (show s ∈ Icc 0 (eVariationOn γ (Icc a b)).toReal ∩ Icc s t from ⟨hs, le_rfl, hst⟩)
      (show t ∈ Icc 0 (eVariationOn γ (Icc a b)).toReal ∩ Icc s t from ⟨ht, hst, le_rfl⟩)
    have hvar := hunit hs ht
    dsimp only [HasUnitSpeedOn, HasConstantSpeedOnWith] at hunit
    simpa only [hvar, NNReal.coe_one, ENNReal.coe_one, one_mul, edist_dist,
      Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using hbound

theorem subsegment_dist_of_unit_lipschitz
    {η : ℝ → M} {L : ℝ} (hL : 0 ≤ L)
    (hlip : LipschitzOnWith 1 η (Icc 0 L))
    (hend : dist (η 0) (η L) = L) :
    ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, dist (η s) (η t) = |s - t| := by
  intro s hs t ht
  wlog hst : s ≤ t generalizing s t
  · rw [dist_comm, abs_sub_comm]
    exact this t ht s hs (le_of_not_ge hst)
  have h0 : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL⟩
  have h1 : L ∈ Icc 0 L := ⟨hL, le_rfl⟩
  have hst' := hlip.dist_le_mul s hs t ht
  have hleft := hlip.dist_le_mul 0 h0 s hs
  have hright := hlip.dist_le_mul t ht L h1
  simp only [NNReal.coe_one, one_mul, Real.dist_eq,
    abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] at hst'
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, zero_sub, abs_neg,
    abs_of_nonneg hs.1] at hleft
  simp only [NNReal.coe_one, one_mul, Real.dist_eq,
    abs_of_nonpos (sub_nonpos.mpr ht.2), neg_sub] at hright
  have htri := dist_triangle (η 0) (η s) (η L)
  have htri' := dist_triangle (η s) (η t) (η L)
  rw [hend] at htri
  rw [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
  linarith

theorem exists_isometric_arcLength_representative
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn γ (Icc a b))
    (hmin : eVariationOn γ (Icc a b) = edist (γ a) (γ b)) :
    ∃ η : ℝ → M,
      η 0 = γ a ∧ η (dist (γ a) (γ b)) = γ b ∧
      η '' Icc 0 (dist (γ a) (γ b)) = γ '' Icc a b ∧
      HasUnitSpeedOn η (Icc 0 (dist (γ a) (γ b))) ∧
      (∀ s ∈ Icc 0 (dist (γ a) (γ b)), ∀ t ∈ Icc 0 (dist (γ a) (γ b)),
        dist (η s) (η t) = |s - t|) := by
  have hv : BoundedVariationOn γ (Icc a b) := by
    rw [BoundedVariationOn, hmin]
    exact edist_ne_top _ _
  obtain ⟨η, h0, h1, himage, hunit, hlip⟩ := exists_arcLength_representative hab hc hv
  have hL : (eVariationOn γ (Icc a b)).toReal = dist (γ a) (γ b) := by
    rw [hmin, ← dist_edist]
  rw [hL] at h1 himage hunit hlip
  refine ⟨η, h0, h1, himage, hunit,
    subsegment_dist_of_unit_lipschitz dist_nonneg hlip ?_⟩
  rw [h0, h1]

end Poincare.MetricCurves
