import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.ComparisonTests
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.RescalingGeometry







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

universe u
namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

namespace RiemannianMetric

theorem pullbackCoefficients_eq_smul_of_inner_scale
    {g h : RiemannianMetric n M} {c : ℝ}
    (hs : ∀ x (v w : TangentSpace (𝓡 n) x), g.inner x v w = c * h.inner x v w)
    (e : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n)) :
    g.pullbackCoefficients e x = c • h.pullbackCoefficients e x := by
  ext v w
  exact hs _ _ _

theorem pullbackVolumeDensity_eq_sqrt_pow_mul_of_inner_scale
    {g h : RiemannianMetric n M} {c : ℝ} (hc : 0 ≤ c)
    (hs : ∀ x (v w : TangentSpace (𝓡 n) x), g.inner x v w = c * h.inner x v w)
    (e : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n)) :
    g.pullbackVolumeDensity e x = Real.sqrt (c ^ n) * h.pullbackVolumeDensity e x := by
  have hmat : Matrix.of (fun i j : Fin n => g.inner (e x)
      (mfderiv (𝓡 n) (𝓡 n) e x (EuclideanSpace.basisFun (Fin n) ℝ i))
      (mfderiv (𝓡 n) (𝓡 n) e x (EuclideanSpace.basisFun (Fin n) ℝ j))) =
      c • Matrix.of (fun i j : Fin n => h.inner (e x)
        (mfderiv (𝓡 n) (𝓡 n) e x (EuclideanSpace.basisFun (Fin n) ℝ i))
        (mfderiv (𝓡 n) (𝓡 n) e x (EuclideanSpace.basisFun (Fin n) ℝ j))) := by
    ext i j
    exact hs _ _ _
  unfold pullbackVolumeDensity
  rw [hmat, Matrix.det_smul, Fintype.card_fin, Real.sqrt_mul (pow_nonneg hc _)]

theorem inverse_pullbackCoefficients_eq_smul_of_inner_scale
    {g h : RiemannianMetric n M} {c : ℝ} (hc : 0 < c)
    (hs : ∀ x (v w : TangentSpace (𝓡 n) x), g.inner x v w = c * h.inner x v w)
    {e : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (he : Function.Injective (mfderiv (𝓡 n) (𝓡 n) e x))
    (a : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    (g.pullbackCoefficients e x).inverse a = c⁻¹ • (h.pullbackCoefficients e x).inverse a := by
  apply (g.isInvertible_pullbackCoefficients he).inverse_apply_eq.mpr
  rw [pullbackCoefficients_eq_smul_of_inner_scale hs]
  simp only [smul_apply, map_smul,
    (h.isInvertible_pullbackCoefficients he).self_apply_inverse, smul_smul,
    inv_mul_cancel₀ hc.ne', one_smul]

end RiemannianMetric

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

namespace AncientRescaling

variable {K : AncientKappaSolution n M} {s : ℝ} (R : AncientRescaling K s)

theorem pullbackVolumeDensity_scale {τ : ℝ} (hτ : 0 < τ)
    (e : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n)) :
    (R.flow.metric (-τ)).pullbackVolumeDensity e x =
      Real.sqrt ((1 / s) ^ n) * (K.flow.metric (0 - s * τ)).pullbackVolumeDensity e x := by
  have hs : ∀ y (v w : TangentSpace (𝓡 n) y),
      (R.flow.metric (-τ)).inner y v w = (1 / s) * (K.flow.metric (0 - s * τ)).inner y v w := by
    intro y v w
    simpa only [mul_neg, zero_sub] using R.metric_scale (-τ) (neg_neg_of_pos hτ) y v w
  exact RiemannianMetric.pullbackVolumeDensity_eq_sqrt_pow_mul_of_inner_scale
    (one_div_pos.mpr R.tau_pos).le hs e x

theorem inverse_pullbackCoefficients_scale {τ : ℝ} (hτ : 0 < τ)
    {e : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (he : Function.Injective (mfderiv (𝓡 n) (𝓡 n) e x))
    (a : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    ((R.flow.metric (-τ)).pullbackCoefficients e x).inverse a =
      s • ((K.flow.metric (0 - s * τ)).pullbackCoefficients e x).inverse a := by
  have hs : ∀ y (v w : TangentSpace (𝓡 n) y),
      (R.flow.metric (-τ)).inner y v w = (1 / s) * (K.flow.metric (0 - s * τ)).inner y v w := by
    intro y v w
    simpa only [mul_neg, zero_sub] using R.metric_scale (-τ) (neg_neg_of_pos hτ) y v w
  simpa only [one_div, inv_inv] using
    RiemannianMetric.inverse_pullbackCoefficients_eq_smul_of_inner_scale
      (one_div_pos.mpr R.tau_pos) hs he a

end AncientRescaling
end PoincareConjecture
