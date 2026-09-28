import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricComparison
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.NormBounds

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {T' T : ℝ}

theorem pullbackCoefficients_exp_bounds
    (F : RicciFlow n M (Ioo T' T)) (hT : T' < 0 ∧ 0 < T)
    (e : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n))
    {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ t ∈ Ioo T' T, (F.connection t).curvatureTensorNorm (e x) ≤ K)
    {t : ℝ} (ht : t ∈ Ioo T' T) (v : EuclideanSpace ℝ (Fin n)) :
    Real.exp (-(2 * (n : ℝ) ^ 3 * K) * (T - T')) *
        (F.metric 0).pullbackCoefficients e x v v ≤
      (F.metric t).pullbackCoefficients e x v v ∧
    (F.metric t).pullbackCoefficients e x v v ≤
      Real.exp ((2 * (n : ℝ) ^ 3 * K) * (T - T')) *
        (F.metric 0).pullbackCoefficients e x v v := by
  let w := mfderiv (𝓡 n) (𝓡 n) e x v
  have hnonneg (τ : ℝ) : 0 ≤ (F.metric τ).inner (e x) w w := by
    by_cases hw : w = 0
    · simp [hw]
    · exact ((F.metric τ).pos (e x) w hw).le
  have hRic : ∀ τ ∈ Ioo T' T, |(F.connection τ).ricci (e x) w w| ≤
      ((n : ℝ) ^ 3 * K) * (F.metric τ).inner (e x) w w := by
    intro τ hτ
    have h := (F.connection τ).abs_ricci_quadratic_le_curvatureTensorNorm (e x) w
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) (e x)) = n :=
      finrank_euclideanSpace_fin
    simp only [Fintype.card_fin, hdim] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hcurv τ hτ) (by positivity)) (hnonneg τ))
  have h := F.metric_inner_self_exp_bounds (convex_Ioo T' T) (Subset.refl _)
    (e x) w ((n : ℝ) ^ 3 * K) hRic hT ht
  have htime : |t - 0| ≤ T - T' := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2, hT.1, hT.2]
  have hC : 0 ≤ 2 * ((n : ℝ) ^ 3 * K) := by positivity
  change Real.exp (-(2 * (n : ℝ) ^ 3 * K) * (T - T')) *
      (F.metric 0).inner (e x) w w ≤ (F.metric t).inner (e x) w w ∧
    (F.metric t).inner (e x) w w ≤
      Real.exp ((2 * (n : ℝ) ^ 3 * K) * (T - T')) * (F.metric 0).inner (e x) w w
  constructor
  · apply le_trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr ?_) (hnonneg 0)) h.1
    nlinarith [mul_le_mul_of_nonneg_left htime hC]
  · apply h.2.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr ?_) (hnonneg 0))
    nlinarith [mul_le_mul_of_nonneg_left htime hC]

end PoincareConjecture.RicciFlow
