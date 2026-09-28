import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.MetricChange
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.Jets.Error

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.SingularRoundComponent

open SingularRegularLimit.RoundComparison

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {epsilon : ℝ}

theorem doubled_accuracy_order_le (N : SingularRoundComponent g epsilon) :
    ⌊(2 * epsilon)⁻¹⌋₊ ≤ ⌊epsilon⁻¹⌋₊ :=
  Nat.floor_mono ((inv_le_inv₀ (mul_pos (by norm_num) N.epsilon_pos) N.epsilon_pos).2
    (by linarith [N.epsilon_pos]))

def changeMetric (N : SingularRoundComponent g epsilon) (h : RiemannianMetric 3 M)
    (herror : ∀ x : N.model.carrier,
      (∑ j ∈ Finset.range (⌊(2 * epsilon)⁻¹⌋₊ + 1),
        (N.model_metric.tensorNorm (N.model_connection.iteratedCovariantTensorDerivative (k := 2)
          (fun y v => (N.normalizedMetricAt h).inner y (v 0) (v 1) -
            N.normalizedMetric.inner y (v 0) (v 1)) j) x) ^ 2) ≤ epsilon ^ 2 / 2) :
    SingularRoundComponent h (2 * epsilon) where
  epsilon_pos := mul_pos (by norm_num) N.epsilon_pos
  basepoint := N.basepoint
  carrier := N.carrier
  component_eq := N.component_eq
  compact := N.compact
  model := N.model
  model_compact := N.model_compact
  model_connected := N.model_connected
  model_metric := N.model_metric
  model_connection := N.model_connection
  model_curvature_one := N.model_curvature_one
  forward := N.forward
  inverse := N.inverse
  forward_image := N.forward_image
  forward_openEmbedding := N.forward_openEmbedding
  forward_smooth := N.forward_smooth
  inverse_smooth := N.inverse_smooth
  left_inverse := N.left_inverse
  right_inverse := N.right_inverse
  scale := N.scale
  scale_pos := N.scale_pos
  metric_comparison := by
    obtain ⟨b, hb, hbound⟩ := N.metric_comparison
    refine ⟨2 * b + epsilon ^ 2, by nlinarith [sq_pos_of_pos N.epsilon_pos], ?_⟩
    intro x
    let S : CovariantTensorEvaluation 3 N.model.carrier 2 := fun y v =>
      N.normalizedMetric.inner y (v 0) (v 1) - N.model_metric.inner y (v 0) (v 1)
    let Q : CovariantTensorEvaluation 3 N.model.carrier 2 := fun y v =>
      (N.normalizedMetricAt h).inner y (v 0) (v 1) - N.normalizedMetric.inner y (v 0) (v 1)
    have hS : IsSmoothCovariantTensor S :=
      (Poincare.RicciFlow.Harnack.metric_isSmoothCovariantTensor N.normalizedMetric).sub
        (Poincare.RicciFlow.Harnack.metric_isSmoothCovariantTensor N.model_metric)
    have hQ : IsSmoothCovariantTensor Q :=
      (Poincare.RicciFlow.Harnack.metric_isSmoothCovariantTensor (N.normalizedMetricAt h)).sub
        (Poincare.RicciFlow.Harnack.metric_isSmoothCovariantTensor N.normalizedMetric)
    have hold : (∑ j ∈ Finset.range (⌊(2 * epsilon)⁻¹⌋₊ + 1),
        (N.model_metric.tensorNorm (N.model_connection.iteratedCovariantTensorDerivative S j) x) ^ 2) ≤ b := by
      apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.add_le_add_right N.doubled_accuracy_order_le 1))
        (fun _ _ _ => sq_nonneg _))
      exact hbound x
    have hadd := sum_iterated_tensorNorm_add_sq_le N.model_connection hS hQ
      ⌊(2 * epsilon)⁻¹⌋₊ x
    have heq : (fun y v => S y v + Q y v) =
        (fun y v => N.scale * singularMetricPullback h N.forward y v -
          N.model_metric.inner y (v 0) (v 1)) := by
      funext y v
      change (N.normalizedMetric.inner y (v 0) (v 1) - N.model_metric.inner y (v 0) (v 1)) +
        (N.scale * singularMetricPullback h N.forward y v -
          N.normalizedMetric.inner y (v 0) (v 1)) = _
      ring
    rw [heq] at hadd
    exact hadd.trans (by nlinarith [herror x])

@[simp] theorem changeMetric_carrier (N : SingularRoundComponent g epsilon)
    (h : RiemannianMetric 3 M) (herror) : (N.changeMetric h herror).carrier = N.carrier := rfl

end PoincareConjecture.SingularRoundComponent
