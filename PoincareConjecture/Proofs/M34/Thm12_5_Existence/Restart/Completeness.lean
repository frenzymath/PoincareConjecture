import PoincareConjecture.Proofs.M34.Thm12_5_Existence.Restart.RicciFlow
import PoincareConjecture.Proofs.M34.Standard.MetricComparisonCompleteness










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34.MetricInteriorCoefficientLimit

variable {ginit : RiemannianMetric 3 StandardCapSpace} {Mfamily : ℕ → Type}
  [∀ k, TopologicalSpace (Mfamily k)] [∀ k, ChartedSpace StandardCapSpace (Mfamily k)]
  [∀ k, IsManifold (𝓡 3) ∞ (Mfamily k)]
  {A : MetricFlowApproximation ginit Mfamily}
  (G : MetricInteriorCoefficientLimit A) (Dinit : LeviCivitaData ginit)



theorem limitMetric_exp_bounds (P : RicciFlowCurvatureTheory.{0})
    {t : ℝ} (ht : t ∈ Ico 0 A.time) (x v : StandardCapSpace) :
    Real.exp (-6 * A.curvature_bound 0 * t) * ginit.inner x v v ≤
        (G.limitMetric Dinit P t).inner x v v ∧
      (G.limitMetric Dinit P t).inner x v v ≤
        Real.exp (6 * A.curvature_bound 0 * t) * ginit.inner x v v := by
  by_cases hzero : t = 0
  · subst t
    simp [G.limitMetric_zero]
  · have htpos : t ∈ Ioo 0 A.time := ⟨lt_of_le_of_ne ht.1 (Ne.symm hzero), ht.2⟩
    have heq := congrArg (fun B => B x v v) (G.limitMetric_coefficients Dinit P t)
    dsimp only at heq
    rw [G.closedCoefficients_of_mem htpos] at heq
    change (G.limitMetric Dinit P t).inner x v v = G.coefficients (t, x) v v at heq
    rw [heq]
    exact G.coefficients_exp_bounds P htpos x v



theorem initial_tangentNorm_le_limit (P : RicciFlowCurvatureTheory.{0})
    {t : ℝ} (ht : t ∈ Ico 0 A.time) (x v : StandardCapSpace) :
    ginit.tangentNorm x v ≤
      Real.exp (3 * A.curvature_bound 0 * t) * (G.limitMetric Dinit P t).tangentNorm x v := by
  have h := mul_le_mul_of_nonneg_left (G.limitMetric_exp_bounds Dinit P ht x v).1
    (Real.exp_nonneg (6 * A.curvature_bound 0 * t))
  have hcancel : Real.exp (6 * A.curvature_bound 0 * t) *
      Real.exp (-6 * A.curvature_bound 0 * t) = 1 := by
    rw [← Real.exp_add, show 6 * A.curvature_bound 0 * t +
      -6 * A.curvature_bound 0 * t = 0 by ring, Real.exp_zero]
  have hmetric : ginit.inner x v v ≤ Real.exp (6 * A.curvature_bound 0 * t) *
      (G.limitMetric Dinit P t).inner x v v := by
    simpa only [← mul_assoc, hcancel, one_mul] using h
  have hexp : Real.exp (6 * A.curvature_bound 0 * t) =
      Real.exp (3 * A.curvature_bound 0 * t) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hsqrt := Real.sqrt_le_sqrt hmetric
  rw [hexp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_nonneg _)] at hsqrt
  exact hsqrt



theorem initialFlow_complete (P : RicciFlowCurvatureTheory.{0})
    (hcomplete : MetricComplete ginit)
    {t : ℝ} (ht : t ∈ Ico 0 A.time) : MetricComplete ((G.initialFlow Dinit P).metric t) := by
  exact RiemannianMetric.metricComplete_of_tangentNorm_comparison
    ginit (G.limitMetric Dinit P t) 0 hcomplete (Real.exp_pos _)
    (G.initial_tangentNorm_le_limit Dinit P ht)

end PoincareConjecture.M34.MetricInteriorCoefficientLimit
