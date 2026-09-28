import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.RoundCurvature.JetBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComparison.Component
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Construction.MetricCombination
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorPullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Algebra

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Topology BigOperators

universe u

namespace PoincareConjecture.SingularRoundComponent

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {epsilon : ℝ} (N : SingularRoundComponent g epsilon)

def modelPartialDiffeomorph : PartialDiffeomorph (𝓡 3) (𝓡 3) N.model.carrier M ∞ where
  toFun := N.forward
  invFun := N.inverse
  source := univ
  target := N.carrier
  map_source' x _ := N.forward_image ▸ mem_range_self x
  map_target' _ _ := mem_univ _
  left_inv' x _ := N.left_inverse x
  right_inv' _x hx := N.right_inverse hx
  open_source := isOpen_univ
  open_target := N.forward_image ▸ N.forward_openEmbedding.isOpen_range
  contMDiffOn_toFun := N.forward_smooth.contMDiffOn
  contMDiffOn_invFun := N.inverse_smooth

theorem forward_isLocalDiffeomorph : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ N.forward :=
  fun _ => ⟨N.modelPartialDiffeomorph, mem_univ _, fun _ _ => rfl⟩

theorem metricError_eq_normalized (x : N.model.carrier)
    (v : Fin 2 → TangentSpace (𝓡 3) x) :
    N.metricError x v = N.normalizedMetric.inner x (v 0) (v 1) -
      N.model_metric.inner x (v 0) (v 1) := rfl

private theorem metric_evaluation_smooth
    {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    (h : RiemannianMetric 3 X) :
    IsSmoothCovariantTensor (fun x (v : Fin 2 → TangentSpace (𝓡 3) x) =>
      h.inner x (v 0) (v 1)) := by
  constructor
  · intro x
    refine ⟨{ toFun := fun v => h.inner x (v 0) (v 1)
              map_update_add' := ?_
              map_update_smul' := ?_ }, fun _ => rfl⟩
    · intro _ v i a b
      fin_cases i <;> simp [Function.update, map_add]
    · intro _ v i c a
      fin_cases i <;> simp [Function.update, map_smul]
  · intro U hU X hX x hx
    have hpair := ((h.contMDiff x).clm_bundle_apply
      ((hX 0 x hx).contMDiffAt (hU.mem_nhds hx))).clm_bundle_apply
      ((hX 1 x hx).contMDiffAt (hU.mem_nhds hx))
    exact (contMDiffAt_totalSpace.mp hpair).2.contMDiffWithinAt

theorem metricError_isSmooth : IsSmoothCovariantTensor N.metricError :=
  (metric_evaluation_smooth N.normalizedMetric).sub (metric_evaluation_smooth N.model_metric)

theorem covariantJet_isSmooth (j : ℕ) :
    IsSmoothCovariantTensor
      (N.model_connection.iteratedCovariantTensorDerivative N.metricError j) :=
  N.model_connection.iteratedCovariantTensorDerivative_isSmooth N.metricError_isSmooth j

theorem covariantJet_evaluation_le (j : ℕ) (hj : j ≤ ⌊epsilon⁻¹⌋₊)
    (x : N.model.carrier) (v : Fin (2 + j) → TangentSpace (𝓡 3) x) :
    |N.model_connection.iteratedCovariantTensorDerivative N.metricError j x v| ≤
      epsilon * ∏ i, N.model_metric.tangentNorm x (v i) := by
  obtain ⟨A, hA⟩ := (N.covariantJet_isSmooth j).1 x
  have he := abs_tensor_evaluation_le_tensorNorm N.model_metric _ x A hA v
  exact he.trans (mul_le_mul_of_nonneg_right (N.covariantJet_norm_lt j hj x).le
    (Finset.prod_nonneg (fun _ _ => Real.sqrt_nonneg _)))

theorem covariantTwoJet_evaluation_le (hepsilon : epsilon ≤ 1 / 200)
    (j : ℕ) (hj : j ≤ 2) (x : N.model.carrier)
    (v : Fin (2 + j) → TangentSpace (𝓡 3) x) :
    |N.model_connection.iteratedCovariantTensorDerivative N.metricError j x v| ≤
      epsilon * ∏ i, N.model_metric.tangentNorm x (v i) :=
  N.covariantJet_evaluation_le j (hj.trans (N.two_le_comparison_order hepsilon)) x v

end PoincareConjecture.SingularRoundComponent
