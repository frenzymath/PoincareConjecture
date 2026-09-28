import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComparison.Component
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.Jets.SphereChart
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.NormBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.SingularRoundComponent

open SingularRegularLimit.RoundComparison

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {epsilon : ℝ}

theorem normalizedMetric_diagonal_error_le (N : SingularRoundComponent g epsilon)
    (x : N.model.carrier) (v : TangentSpace (𝓡 3) x) :
    |N.normalizedMetric.inner x v v - N.model_metric.inner x v v| ≤
      epsilon * N.model_metric.inner x v v := by
  let E : CovariantTensorEvaluation 3 N.model.carrier 2 := fun y w =>
    N.normalizedMetric.inner y (w 0) (w 1) - N.model_metric.inner y (w 0) (w 1)
  have hs : IsSmoothCovariantTensor E :=
    (Poincare.RicciFlow.Harnack.metric_isSmoothCovariantTensor N.normalizedMetric).sub
      (Poincare.RicciFlow.Harnack.metric_isSmoothCovariantTensor N.model_metric)
  obtain ⟨A, hA⟩ := hs.1 x
  have h := abs_tensor_evaluation_le_tensorNorm N.model_metric E x A hA (fun _ => v)
  have hn : ∏ _ : Fin 2, N.model_metric.tangentNorm x v = N.model_metric.inner x v v := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    change (Real.sqrt (N.model_metric.inner x v v)) ^ 2 = _
    apply Real.sq_sqrt
    by_cases hv : v = 0
    · simp [hv]
    · exact (N.model_metric.pos x v hv).le
  rw [hn] at h
  have hnorm : N.model_metric.tensorNorm E x ≤ epsilon :=
    (N.normalizedMetric_error_norm_lt (r := 0) (Nat.zero_le _) x).le
  have hnonneg : 0 ≤ N.model_metric.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (N.model_metric.pos x v hv).le
  exact h.trans (mul_le_mul_of_nonneg_right hnorm hnonneg)

theorem normalizedMetric_centered_ellipticity (N : SingularRoundComponent g epsilon)
    (hepsilon : epsilon ≤ roundComparisonThreshold)
    {f : EuclideanSpace ℝ (Fin 3) → N.model.carrier}
    (hmetric : ∀ v w : EuclideanSpace ℝ (Fin 3),
      sphereReferenceMetric.inner 0 v w = N.model_metric.inner (f 0)
        (mfderiv (𝓡 3) (𝓡 3) f 0 v) (mfderiv (𝓡 3) (𝓡 3) f 0 w))
    (v : EuclideanSpace ℝ (Fin 3)) :
    (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ N.normalizedMetric.pullbackCoefficients f 0 v v ∧
      N.normalizedMetric.pullbackCoefficients f 0 v v ≤ 2 * ‖v‖ ^ 2 := by
  have h := N.normalizedMetric_diagonal_error_le (f 0) (mfderiv (𝓡 3) (𝓡 3) f 0 v)
  rw [← hmetric v v, sphereReferenceMetric_inner_zero, real_inner_self_eq_norm_sq] at h
  change |N.normalizedMetric.pullbackCoefficients f 0 v v - ‖v‖ ^ 2| ≤
    epsilon * ‖v‖ ^ 2 at h
  obtain ⟨hl, hu⟩ := abs_le.mp h
  have he : epsilon ≤ 1 / 200 := hepsilon.trans roundComparisonThreshold_le
  have hsmall := mul_le_mul_of_nonneg_right he (sq_nonneg ‖v‖)
  constructor <;> linarith [sq_nonneg ‖v‖]

end PoincareConjecture.SingularRoundComponent
