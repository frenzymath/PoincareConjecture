import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.SmallCompactness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.SmallProperties











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
attribute [local instance] smallCarrier smallChartedSpace smallIsManifold



theorem exists_nonflat_ancient_limit_of_small_expanding_cylinders
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    (C : ℕ → FlowCarrier.{u} (m + 1)) (J : ℕ → Set ℝ)
    (F : ∀ k, RicciFlow (m + 1) (C k).carrier (J k))
    (p : ∀ k, (C k).carrier) (A L : ℕ → ℝ)
    (hA : Tendsto A atTop atTop) (hL : Tendsto L atTop atTop)
    (hJ : ∀ k, Icc (-A k) 0 ⊆ interior (J k))
    (hcomplete : ∀ k, ∀ t ∈ Icc (-A k) 0, MetricComplete ((F k).metric t))
    (hoperator : ∀ k, ∀ t ∈ Icc (-A k) 0, ∀ x : (C k).carrier,
      ((F k).connection t).NonnegativeCurvatureOperator x)
    (hscalar : ∀ k, ∀ t ∈ Icc (-A k) 0,
      ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
        ((F k).connection t).scalarCurvature x ≤ 4)
    (hnormalize : ∀ k, ((F k).connection 0).scalarCurvature (p k) = 1)
    {ν : ℝ} (hν : 0 < ν)
    (hvolume : ∀ᶠ k in atTop, ENNReal.ofReal ν ≤
      ((F k).metric 0).volumeMeasure (((F k).metric 0).ball (p k) 1)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∃ G : AncientPointedGeometricConvergence (fun k => (C k).shrink)
        (fun k t => (F k).shrink.metric (t - δ))
        (fun k => equivShrink (C k).carrier (p k)) δ,
        (∀ t ∈ Iio δ, G.limitCarrier.metricComplete (G.limitFlow.metric t)) ∧
        (0 < (G.limitFlow.connection 0).curvatureTensorNorm G.base ∧
         (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
           (G.limitFlow.connection t).curvatureTensorNorm x ≤
             ((m + 1 : ℕ) : ℝ) ^ 2 * 4) ∧
         (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
           (G.limitFlow.connection t).NonnegativeCurvatureOperator x)) := by
  obtain ⟨δ, hδ, hδone, hbuffer⟩ := exists_scalar_buffer_of_expanding_cylinders
    hC hm C J F p A L hA hL hJ hcomplete hoperator hscalar hnormalize
  obtain ⟨G, hzero⟩ := exists_complete_ancient_limit_of_small_expanding_cylinders
    hC hm C J F p A L hA hL hJ hcomplete hoperator hscalar hν hvolume hδ hδone
  obtain ⟨hGcomplete, hGnorm, hGoperator⟩ :=
    ancient_limit_properties_of_small_expanding_cylinders
      hC C J F p A L hA hL hJ hoperator hscalar hδ G hzero
  have hsmallbuffer : ∀ᶠ k in atTop,
      (1 : ℝ) / 2 ≤ (((F k).shrink.bufferedExpandingFlow δ).connection 0).scalarCurvature
        (equivShrink (C k).carrier (p k)) := by
    filter_upwards [hbuffer] with k hk
    simpa only [bufferedExpandingFlow_connection, shrink_scalarCurvature,
      Equiv.symm_apply_apply] using hk
  have hquant := AncientPointedGeometricConvergence.scalar_lower_bound_le_mul_base_curvatureTensorNorm
    (C := fun k => (C k).shrink)
    (fun k => (F k).shrink.bufferedExpandingFlow δ) G hδ
    (eventually_buffered_time_window J A hA hJ δ) hsmallbuffer
  refine ⟨δ, hδ, hδone, G, hGcomplete, ?_, hGnorm, hGoperator⟩
  by_contra h
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos
    (sq_nonneg (((m + 1 : ℕ) : ℝ))) (le_of_not_gt h)
  linarith

end PoincareConjecture.RicciFlow
