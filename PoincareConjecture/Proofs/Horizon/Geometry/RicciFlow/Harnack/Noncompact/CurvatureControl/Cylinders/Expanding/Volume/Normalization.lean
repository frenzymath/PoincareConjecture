import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.Volume.Components
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.Normalization








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



theorem exists_positive_volume_ancient_limit_of_rescaled_expanding_cylinders_components
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    (M : ℕ → Type u) [∀ k, TopologicalSpace (M k)] [∀ k, MeasurableSpace (M k)]
    [∀ k, BorelSpace (M k)] [∀ k, T3Space (M k)] [∀ k, SecondCountableTopology (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) (M k)]
    [∀ k, IsManifold (𝓡 (m + 1)) ∞ (M k)]
    (J : ℕ → Set ℝ) (F : ∀ k, RicciFlow (m + 1) (M k) (J k))
    (p : ∀ k, M k) (Q τ A L : ℕ → ℝ)
    (hQ : ∀ k, 0 < Q k) (hA : Tendsto A atTop atTop) (hL : Tendsto L atTop atTop)
    (hJ : ∀ k, Icc (τ k + (-A k) / Q k) (τ k) ⊆ interior (J k))
    (hcomplete : ∀ k, ∀ t ∈ Icc (τ k + (-A k) / Q k) (τ k),
      MetricComplete ((F k).metric t))
    (hoperator : ∀ k, ∀ t ∈ Icc (τ k + (-A k) / Q k) (τ k),
      ∀ x : M k, ((F k).connection t).NonnegativeCurvatureOperator x)
    (hscalar : ∀ k, ∀ t ∈ Icc (τ k + (-A k) / Q k) (τ k),
      ∀ x ∈ ((F k).metric (τ k)).ball (p k) (L k / Real.sqrt (Q k)),
        ((F k).connection t).scalarCurvature x ≤ 4 * Q k)
    (hnormalize : ∀ k, ((F k).connection (τ k)).scalarCurvature (p k) = Q k)
    {ν : ℝ} (hν : 0 < ν)
    (hfailure : ∀ r : ℝ, 0 < r → ∃ᶠ k in atTop,
      ENNReal.ofReal (ν * (r / Real.sqrt (Q k)) ^ (m + 1)) ≤
        ((F k).metric (τ k)).volumeMeasure
          (((F k).metric (τ k)).ball (p k) (r / Real.sqrt (Q k)))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∃ G : AncientPointedGeometricConvergence
        (fun k => (componentFlowCarrier (n := m + 1) (p (σ k))).shrink)
        (fun k t => (((F (σ k)).rescaledTerminalFlow (Q (σ k)) (hQ (σ k)) (τ (σ k))).restrictComponent
          (p (σ k))).shrink.metric (t - δ))
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
  have htime (k : ℕ) (s : ℝ) (hs : s ∈ Icc (-A k) 0) :
      τ k + s / Q k ∈ Icc (τ k + (-A k) / Q k) (τ k) := by
    constructor
    · exact _root_.add_le_add le_rfl (div_le_div_of_nonneg_right hs.1 (hQ k).le)
    · simpa using _root_.add_le_add (le_refl (τ k))
        (div_le_div_of_nonneg_right hs.2 (hQ k).le)
  apply exists_positive_volume_ancient_limit_of_expanding_cylinders_components (ν := ν)
    hC hm M (fun k => (fun s : ℝ => τ k + s / Q k) ⁻¹' J k)
    (fun k => (F k).rescaledTerminalFlow (Q k) (hQ k) (τ k)) p A L hA hL
    (fun k => (F k).rescaledTerminalFlow_interior (hQ k) (hJ k))
    (fun k s hs => metricComplete_rescaledMetric _ (Q k) (hQ k)
      (hcomplete k _ (htime k s hs)))
    (fun k s hs x => rescaledMetric_nonnegativeCurvatureOperator _ _ (Q k) (hQ k) x
      (hoperator k _ (htime k s hs) x))
    (fun k => (F k).rescaledTerminalFlow_scalar_le_four
      (Q k) (hQ k) (τ k) (-A k) (L k) (p k) (hscalar k))
    (fun k => (F k).rescaledTerminalFlow_scalar_zero
      (Q k) (hQ k) (τ k) (p k) (hnormalize k)) hν
  intro r hr
  apply (hfailure r hr).mono
  intro k hk
  exact (F k).rescaledTerminalFlow_ball_volume_lower_bound
    (Q k) (hQ k) (τ k) (p k) r ν hk

end PoincareConjecture.RicciFlow
