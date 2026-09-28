import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.Volume.Limit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RicciFlow

attribute [local instance] smallCarrier smallChartedSpace smallIsManifold
attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t3Space FlowCarrier.secondCountable

theorem exists_positive_volume_ancient_limit_of_expanding_cylinders_components
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    (M : ℕ → Type u) [∀ k, TopologicalSpace (M k)] [∀ k, MeasurableSpace (M k)]
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
    (hfailure : ∀ r : ℝ, 0 < r → ∃ᶠ k in atTop, ENNReal.ofReal (ν * r ^ (m + 1)) ≤
      ((F k).metric 0).volumeMeasure (((F k).metric 0).ball (p k) r)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∃ G : AncientPointedGeometricConvergence
        (fun k => (componentFlowCarrier (n := m + 1) (p (σ k))).shrink)
        (fun k t => ((F (σ k)).restrictComponent (p (σ k))).shrink.metric (t - δ))
        (fun k => equivShrink (componentFlowCarrier (n := m + 1) (p (σ k))).carrier
          (componentFlowBase (n := m + 1) (p (σ k)))) δ,
        (∀ t ∈ Iio δ, G.limitCarrier.metricComplete (G.limitFlow.metric t)) ∧
        (0 < (G.limitFlow.connection 0).curvatureTensorNorm G.base ∧
         (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
           (G.limitFlow.connection t).curvatureTensorNorm x ≤
             ((m + 1 : ℕ) : ℝ) ^ 2 * 4) ∧
         (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
           (G.limitFlow.connection t).NonnegativeCurvatureOperator x)) ∧
        (∀ r : ℝ, 0 < r → ENNReal.ofReal ((ν / 2 ^ (m + 1)) * r ^ (m + 1)) ≤
          (G.limitFlow.metric 0).volumeMeasure ((G.limitFlow.metric 0).ball G.base r)) := by
  apply exists_positive_volume_ancient_limit_of_expanding_cylinders (ν := ν) hC hm
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
  · intro r hr
    apply (hfailure r hr).mono
    intro k hk
    rwa [(F k).restrictComponent_volumeMeasure_ball]

end PoincareConjecture.RicciFlow
