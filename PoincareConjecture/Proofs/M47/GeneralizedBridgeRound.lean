import PoincareConjecture.Proofs.M47.GeneralizedBridgeIsometry
import PoincareConjecture.Proofs.M47.GeneralizedBridgeTopology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

section Isometry

variable {M X : Type u} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 X}

noncomputable def metricIsometry_pullback_round_component
    (f : Diffeomorph (𝓡 3) (𝓡 3) M X ∞) (hf : MetricHomothety g h f 1)
    {epsilon : ℝ} (N : SingularRoundComponent h epsilon) :
    SingularRoundComponent g epsilon := by
  have hi := metricHomothety_one_symm f hf
  have hpullback : singularMetricPullback g (f.symm ∘ N.forward) =
      singularMetricPullback h N.forward := by
    funext y v
    unfold singularMetricPullback
    rw [f.symm.mfderiv_comp (by simp)]
    simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply, one_mul] using
      hi (N.forward y) (mfderiv (𝓡 3) (𝓡 3) N.forward y (v 0))
        (mfderiv (𝓡 3) (𝓡 3) N.forward y (v 1))
  refine {
    epsilon_pos := N.epsilon_pos
    basepoint := f.symm N.basepoint
    carrier := f.symm '' N.carrier
    component_eq := by rw [N.component_eq]; exact diffeomorph_image_connectedComponent f.symm _
    compact := N.compact.image f.symm.continuous
    model := N.model
    model_compact := N.model_compact
    model_connected := N.model_connected
    model_metric := N.model_metric
    model_connection := N.model_connection
    model_curvature_one := N.model_curvature_one
    forward := f.symm ∘ N.forward
    inverse := N.inverse ∘ f
    forward_image := by rw [range_comp, N.forward_image]
    forward_openEmbedding := f.symm.toHomeomorph.isOpenEmbedding.comp N.forward_openEmbedding
    forward_smooth := f.symm.contMDiff.comp N.forward_smooth
    inverse_smooth := N.inverse_smooth.comp f.contMDiff.contMDiffOn ?_
    left_inverse := ?_
    right_inverse := ?_
    scale := N.scale
    scale_pos := N.scale_pos
    metric_comparison := by rw [hpullback]; exact N.metric_comparison
  }
  · rintro _ ⟨x, hx, rfl⟩
    change f (f.symm x) ∈ N.carrier
    rw [f.apply_symm_apply]
    exact hx
  · intro y
    simp only [Function.comp_apply, f.apply_symm_apply, N.left_inverse y]
  · rintro _ ⟨x, hx, rfl⟩
    simp only [Function.comp_apply, f.apply_symm_apply, N.right_inverse hx]

end Isometry

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
  (H : M33RegularHistoryData W) {t : ℝ} (ht : t ∈ H.generalized.interval)
  (hregular : t ∉ F.surgery_times)

include hregular

theorem regular_history_round_control {epsilon C : ℝ}
    (x : (H.generalized.slice t).carrier) (N : SingularRoundComponent (F.metric t) epsilon)
    (hx : H.history.forward t ht x ∈ N.carrier) :
    Nonempty (GeneralizedCanonicalControl (F := H.generalized) t x epsilon C) := by
  let f := regular_history_slice_diffeomorph H t ht hregular
  have hf : MetricHomothety (H.generalized.metric t) (F.metric t) f 1 := by
    intro y v w
    change (F.metric t).inner (H.history.forward t ht y)
      (mfderiv (𝓡 3) (𝓡 3) (H.history.forward t ht) y v)
      (mfderiv (𝓡 3) (𝓡 3) (H.history.forward t ht) y w) = _
    rw [H.history.metric_pullback, one_mul]
  refine ⟨GeneralizedCanonicalControl.round (metricIsometry_pullback_round_component f hf N) ?_⟩
  exact ⟨f x, hx, f.symm_apply_apply x⟩

end PoincareConjecture.M47
