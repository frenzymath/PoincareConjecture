import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.Compactness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.Properties
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Components

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

theorem exists_nonflat_ancient_limit_of_expanding_cylinders
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{0}) (hm : 0 < m)
    (C : ℕ → FlowCarrier.{0} (m + 1)) (J : ℕ → Set ℝ)
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
      ∃ G : AncientPointedGeometricConvergence C
        (fun k t => (F k).metric (t - δ)) p δ,
        (∀ t ∈ Iio δ, G.limitCarrier.metricComplete (G.limitFlow.metric t)) ∧
        (0 < (G.limitFlow.connection 0).curvatureTensorNorm G.base ∧
         (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
           (G.limitFlow.connection t).curvatureTensorNorm x ≤
             ((m + 1 : ℕ) : ℝ) ^ 2 * 4) ∧
         (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
           (G.limitFlow.connection t).NonnegativeCurvatureOperator x)) := by
  obtain ⟨δ, hδ, hδone, hbuffer⟩ := exists_scalar_buffer_of_expanding_cylinders
    hC hm C J F p A L hA hL hJ hcomplete hoperator hscalar hnormalize
  obtain ⟨G, hzero⟩ := exists_complete_ancient_limit_of_expanding_cylinders
    hC hm C J F p A L hA hL hJ hcomplete hoperator hscalar hν hvolume hδ hδone
  obtain ⟨hGcomplete, hGnorm, hGoperator⟩ := ancient_limit_properties_of_expanding_cylinders
    hC C J F p A L hA hL hJ hoperator hscalar hδ G hzero
  have hquant := G.scalar_lower_bound_le_mul_base_curvatureTensorNorm
    (fun k => (F k).bufferedExpandingFlow δ) hδ
    (eventually_buffered_time_window J A hA hJ δ) hbuffer
  refine ⟨δ, hδ, hδone, G, hGcomplete, ?_, hGnorm, hGoperator⟩
  by_contra h
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos
    (sq_nonneg (((m + 1 : ℕ) : ℝ)))
    (le_of_not_gt h)
  linarith

theorem exists_nonflat_ancient_limit_of_expanding_cylinders_components
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{0}) (hm : 0 < m)
    (M : ℕ → Type) [∀ k, TopologicalSpace (M k)] [∀ k, MeasurableSpace (M k)]
    [∀ k, BorelSpace (M k)] [∀ k, T3Space (M k)] [∀ k, SecondCountableTopology (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) (M k)]
    [∀ k, IsManifold (𝓡 (m + 1)) ∞ (M k)]
    (J : ℕ → Set ℝ) (F : ∀ k, RicciFlow (m + 1) (M k) (J k))
    (p : ∀ k, M k) (A L : ℕ → ℝ)
    (hA : Tendsto A atTop atTop) (hL : Tendsto L atTop atTop)
    (hJ : ∀ k, Icc (-A k) 0 ⊆ interior (J k))
    (hcomplete : ∀ k, ∀ t ∈ Icc (-A k) 0, MetricComplete ((F k).metric t))
    (hoperator : ∀ k, ∀ t ∈ Icc (-A k) 0, ∀ x : M k,
      ((F k).connection t).NonnegativeCurvatureOperator x)
    (hscalar : ∀ k, ∀ t ∈ Icc (-A k) 0,
      ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
        ((F k).connection t).scalarCurvature x ≤ 4)
    (hnormalize : ∀ k, ((F k).connection 0).scalarCurvature (p k) = 1)
    {ν : ℝ} (hν : 0 < ν)
    (hvolume : ∀ᶠ k in atTop, ENNReal.ofReal ν ≤
      ((F k).metric 0).volumeMeasure (((F k).metric 0).ball (p k) 1)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∃ G : AncientPointedGeometricConvergence
        (fun k => componentFlowCarrier (n := m + 1) (p k))
        (fun k t => ((F k).restrictComponent (p k)).metric (t - δ))
        (fun k => componentFlowBase (n := m + 1) (p k)) δ,
        (∀ t ∈ Iio δ, G.limitCarrier.metricComplete (G.limitFlow.metric t)) ∧
        (letI := G.limitCarrier.topologicalSpace
         letI := G.limitCarrier.chartedSpace
         letI := G.limitCarrier.isManifold
         0 < (G.limitFlow.connection 0).curvatureTensorNorm G.base ∧
         (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
           (G.limitFlow.connection t).curvatureTensorNorm x ≤
             ((m + 1 : ℕ) : ℝ) ^ 2 * 4) ∧
         (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
           (G.limitFlow.connection t).NonnegativeCurvatureOperator x)) := by
  apply exists_nonflat_ancient_limit_of_expanding_cylinders (ν := ν) hC hm
    (fun k => componentFlowCarrier (n := m + 1) (p k)) J
    (fun k => (F k).restrictComponent (p k))
    (fun k => componentFlowBase (n := m + 1) (p k)) A L hA hL hJ
    (fun k t ht => (F k).restrictComponent_metricComplete (p k) t (hcomplete k t ht))
    (fun k t ht x => ((F k).restrictComponent_nonnegativeCurvatureOperator_iff
      (p k) t x).mpr (hoperator k t ht x))
  · intro k t ht x hx
    rw [(F k).restrictComponent_scalarCurvature]
    apply hscalar k t ht x
    change (((F k).restrictComponent (p k)).metric 0).edist
      (componentFlowBase (n := m + 1) (p k)) x < ENNReal.ofReal (L k) at hx
    rwa [(F k).restrictComponent_edist] at hx
  · intro k
    rw [(F k).restrictComponent_scalarCurvature]
    exact hnormalize k
  · exact hν
  · filter_upwards [hvolume] with k hk
    rwa [(F k).restrictComponent_volumeMeasure_ball]

end PoincareConjecture.RicciFlow
