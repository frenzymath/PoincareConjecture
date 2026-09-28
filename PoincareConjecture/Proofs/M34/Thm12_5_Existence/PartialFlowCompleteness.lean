import PoincareConjecture.Definitions.M34StandardCapExistence
import PoincareConjecture.Statements.Ch04.CurvatureTheory
import PoincareConjecture.Proofs.M34.Standard.MetricComparisonCompleteness

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

variable {g0 : StandardInitialMetric} (F : PartialStandardCapFlow g0)

theorem partialFlow_exp_bounds (P : RicciFlowCurvatureTheory.{0})
    {t K : ℝ} (ht : t ∈ Ico 0 F.lifetime) (hK : 0 ≤ K)
    (hfull : ∀ s ∈ Icc 0 t, ∀ x : StandardCapSpace,
      (F.flow.connection s).curvatureTensorNorm x ≤ K) (x v : StandardCapSpace) :
    Real.exp (-6 * K * t) * g0.metric.inner x v v ≤ (F.flow.metric t).inner x v v ∧
      (F.flow.metric t).inner x v v ≤ Real.exp (6 * K * t) * g0.metric.inner x v v := by
  have h := P.metric_comparison 3 StandardCapSpace (Ico 0 F.lifetime) F.flow
    0 t K ⟨le_rfl, F.lifetime_pos⟩ ht ht.1 hK hfull x v
  rw [F.initial_metric] at h
  norm_num at h ⊢
  exact h

theorem partialFlow_initial_tangentNorm_le (P : RicciFlowCurvatureTheory.{0})
    {t K : ℝ} (ht : t ∈ Ico 0 F.lifetime) (hK : 0 ≤ K)
    (hfull : ∀ s ∈ Icc 0 t, ∀ x : StandardCapSpace,
      (F.flow.connection s).curvatureTensorNorm x ≤ K) (x v : StandardCapSpace) :
    g0.metric.tangentNorm x v ≤ Real.exp (3 * K * t) * (F.flow.metric t).tangentNorm x v := by
  have h := mul_le_mul_of_nonneg_left (partialFlow_exp_bounds F P ht hK hfull x v).1
    (Real.exp_nonneg (6 * K * t))
  have hcancel : Real.exp (6 * K * t) * Real.exp (-6 * K * t) = 1 := by
    rw [← Real.exp_add, show 6 * K * t + -6 * K * t = 0 by ring, Real.exp_zero]
  have hmetric : g0.metric.inner x v v ≤
      Real.exp (6 * K * t) * (F.flow.metric t).inner x v v := by
    simpa only [← mul_assoc, hcancel, one_mul] using h
  have hexp : Real.exp (6 * K * t) = Real.exp (3 * K * t) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hsqrt := Real.sqrt_le_sqrt hmetric
  rw [hexp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_nonneg _)] at hsqrt
  exact hsqrt

theorem partialFlow_complete (P : RicciFlowCurvatureTheory.{0})
    {t : ℝ} (ht : t ∈ Ico 0 F.lifetime) : MetricComplete (F.flow.metric t) := by
  obtain ⟨K, hK, hbound⟩ := F.curvature_locally_bounded t ht.1 ht.2
  exact RiemannianMetric.metricComplete_of_tangentNorm_comparison
    g0.metric (F.flow.metric t) 0 g0.complete (Real.exp_pos _)
    (partialFlow_initial_tangentNorm_le F P ht hK
      (fun s hs x => (le_abs_self _).trans (hbound s hs x)))

end PoincareConjecture.M34
