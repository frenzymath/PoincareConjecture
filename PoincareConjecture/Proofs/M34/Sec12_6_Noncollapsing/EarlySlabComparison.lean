import PoincareConjecture.Proofs.M34.Standard.CalibratedMetricComparison
import PoincareConjecture.Proofs.M34.Thm12_5_Existence.PartialFlowCompleteness

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture.M34

variable {g0 : StandardInitialMetric} (F : PartialStandardCapFlow g0)

theorem partialFlow_uniform_tangentNorm_comparison (P : RicciFlowCurvatureTheory.{0})
    {T : ℝ} (hT : T ∈ Ico 0 F.lifetime) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ t ∈ Icc 0 T, ∀ x v : StandardCapSpace,
      g0.metric.tangentNorm x v ≤ c * (F.flow.metric t).tangentNorm x v ∧
      (F.flow.metric t).tangentNorm x v ≤ c * g0.metric.tangentNorm x v := by
  obtain ⟨K, hK, hfull⟩ := F.curvature_locally_bounded T hT.1 hT.2
  let c : ℝ := Real.exp (3 * K * T)
  have hc : 1 ≤ c := Real.one_le_exp (mul_nonneg (by positivity) hT.1)
  refine ⟨c, hc, ?_⟩
  intro t ht x v
  have htime : t ∈ Ico 0 F.lifetime := ⟨ht.1, ht.2.trans_lt hT.2⟩
  have hbound : ∀ s ∈ Icc 0 t, ∀ y : StandardCapSpace,
      (F.flow.connection s).curvatureTensorNorm y ≤ K :=
    fun s hs y => (le_abs_self _).trans (hfull s ⟨hs.1, hs.2.trans ht.2⟩ y)
  have hexp : Real.exp (3 * K * t) ≤ c := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left ht.2 (by positivity)
  constructor
  · exact (partialFlow_initial_tangentNorm_le F P htime hK hbound x v).trans
      (mul_le_mul_of_nonneg_right hexp (Real.sqrt_nonneg _))
  · have h := Real.sqrt_le_sqrt (partialFlow_exp_bounds F P htime hK hbound x v).2
    have heq : Real.exp (6 * K * t) = Real.exp (3 * K * t) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
      ring
    rw [heq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_nonneg _)] at h
    exact h.trans (mul_le_mul_of_nonneg_right hexp (Real.sqrt_nonneg _))

theorem partialFlow_uniform_metric_volume_comparison (P : RicciFlowCurvatureTheory.{0})
    {T : ℝ} (hT : T ∈ Ico 0 F.lifetime) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ t ∈ Icc 0 T,
      (∀ x y, g0.metric.edist x y ≤ ENNReal.ofReal c * (F.flow.metric t).edist x y) ∧
      (∀ x y, (F.flow.metric t).edist x y ≤ ENNReal.ofReal c * g0.metric.edist x y) ∧
      (∀ A, calibratedMetricVolume g0.metric A ≤
        ENNReal.ofReal c ^ 3 * calibratedMetricVolume (F.flow.metric t) A) ∧
      (∀ A, calibratedMetricVolume (F.flow.metric t) A ≤
        ENNReal.ofReal c ^ 3 * calibratedMetricVolume g0.metric A) := by
  obtain ⟨c, hc, hnorm⟩ := partialFlow_uniform_tangentNorm_comparison F P hT
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  refine ⟨c, hc, fun t ht => ?_⟩
  exact ⟨edist_le_of_tangentNorm_le _ _ hcpos (fun x v => (hnorm t ht x v).1),
    edist_le_of_tangentNorm_le _ _ hcpos (fun x v => (hnorm t ht x v).2),
    calibratedMetricVolume_le_of_tangentNorm_le _ _ hcpos
      (fun x v => (hnorm t ht x v).1),
    calibratedMetricVolume_le_of_tangentNorm_le _ _ hcpos
      (fun x v => (hnorm t ht x v).2)⟩

end PoincareConjecture.M34
