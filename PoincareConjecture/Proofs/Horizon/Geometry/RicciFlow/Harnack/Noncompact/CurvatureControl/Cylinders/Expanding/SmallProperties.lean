import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Preservation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Completeness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.Source
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.SmallCarrier









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.secondCountable
attribute [local instance] smallCarrier smallChartedSpace smallIsManifold



theorem ancient_limit_properties_of_small_expanding_cylinders
    {n : ℕ} (hC : RicciFlowCurvatureTheory.{u})
    (C : ℕ → FlowCarrier.{u} n) (J : ℕ → Set ℝ)
    (F : ∀ k, RicciFlow n (C k).carrier (J k)) (p : ∀ k, (C k).carrier)
    (A L : ℕ → ℝ) (hA : Tendsto A atTop atTop) (hL : Tendsto L atTop atTop)
    (hJ : ∀ k, Icc (-A k) 0 ⊆ interior (J k))
    (hoperator : ∀ k, ∀ t ∈ Icc (-A k) 0, ∀ x : (C k).carrier,
      ((F k).connection t).NonnegativeCurvatureOperator x)
    (hscalar : ∀ k, ∀ t ∈ Icc (-A k) 0,
      ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
        ((F k).connection t).scalarCurvature x ≤ 4)
    {δ : ℝ} (hδ : 0 < δ)
    (G : AncientPointedGeometricConvergence (fun k => (C k).shrink)
      (fun k t => (F k).shrink.metric (t - δ))
      (fun k => equivShrink (C k).carrier (p k)) δ)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0)) :
    (∀ t ∈ Iio δ, G.limitCarrier.metricComplete (G.limitFlow.metric t)) ∧
    (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
      (G.limitFlow.connection t).curvatureTensorNorm x ≤ (n : ℝ) ^ 2 * 4) ∧
    (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
      (G.limitFlow.connection t).NonnegativeCurvatureOperator x) := by
  let Fseq := fun k => (F k).shrink.bufferedExpandingFlow δ
  have htime := eventually_buffered_time_window J A hA hJ δ
  have hnorm : ∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
      (G.limitFlow.connection t).curvatureTensorNorm x ≤ (n : ℝ) ^ 2 * 4 := by
    apply AncientPointedGeometricConvergence.curvatureTensorNorm_le_of_uniform_ball_bound
      (C := fun k => (C k).shrink) Fseq G hδ htime
    intro a b hb R _
    filter_upwards [hA.eventually_ge_atTop (δ - a), hL.eventually_ge_atTop R]
      with k hkA hkL t ht x hx
    have hs : t - δ ∈ Icc (-A k) 0 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    change ((F k).shrink.connection (t - δ)).curvatureTensorNorm x ≤ _
    rw [shrink_curvatureTensorNorm]
    apply (F k).curvatureTensorNorm_le_on_two_time_ball_of_terminal_cylinder hC
      (hJ k) (hoperator k) (p k) (hscalar k) hs hs hkL
    change ((F k).shrink.metric (t - δ)).edist
      (equivShrink (C k).carrier (p k)) x < ENNReal.ofReal R at hx
    simpa only [RiemannianMetric.ball, mem_ofPred_eq, shrink_edist,
      Equiv.symm_apply_apply] using hx
  refine ⟨metricComplete_of_ancient_uniform_curvature_bound G.limitCarrier hδ
    G.limitFlow G.base hcomplete (by positivity) hnorm, hnorm, ?_⟩
  apply AncientPointedGeometricConvergence.nonnegativeCurvatureOperator_of_eventually
    (C := fun k => (C k).shrink) Fseq G hδ htime
  intro t ht
  filter_upwards [hA.eventually_ge_atTop (δ - t)] with k hk x
  apply ((F k).shrink_nonnegativeCurvatureOperator_iff (t - δ) x).mpr
  exact hoperator k (t - δ) ⟨by linarith, by linarith [show t < δ from ht]⟩
    ((equivShrink (C k).carrier).symm x)

end PoincareConjecture.RicciFlow
