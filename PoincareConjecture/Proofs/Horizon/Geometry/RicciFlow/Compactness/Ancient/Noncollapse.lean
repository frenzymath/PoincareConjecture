import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Restriction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.Noncollapse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.AncientPointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t3Space FlowCarrier.secondCountable

theorem volume_lower_bound_of_static_noncollapse
    {n : ℕ} {C : ℕ → FlowCarrier.{0} n} {J : ℕ → Set ℝ}
    (F : ∀ k, RicciFlow n (C k).carrier (J k)) {p : ∀ k, (C k).carrier} {T : ℝ}
    (G : AncientPointedGeometricConvergence C (fun k => (F k).metric) p T)
    (hT : 0 < T)
    (htime : ∀ a b : ℝ, b < T → ∀ᶠ k in atTop, Icc a b ⊆ J k)
    (hcomplete : ∀ t ∈ Iio T, G.limitCarrier.metricComplete (G.limitFlow.metric t))
    (κ : ℝ)
    (hsource : ∀ t ∈ Iio T, ∀ᶠ k in atTop, ∀ x : (C k).carrier, ∀ r : ℝ, 0 < r →
      (∀ y ∈ ((F k).metric t).ball x r,
        |((F k).connection t).curvatureTensorNorm y| ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤ ((F k).metric t).volumeMeasure (((F k).metric t).ball x r)) :
    ∀ t ∈ Iio T, ∀ x : G.limitCarrier.carrier, ∀ r : ℝ, 0 < r →
      (∀ y ∈ (G.limitFlow.metric t).ball x r,
        |(G.limitFlow.connection t).curvatureTensorNorm y| ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤
        (G.limitFlow.metric t).volumeMeasure ((G.limitFlow.metric t).ball x r) := by
  intro t ht x r hr hcurv
  obtain ⟨a, b, ha, hb, hbT, htw⟩ := exists_ancient_window_of_isCompact hT
    isCompact_singleton (singleton_subset_iff.mpr ht)
  obtain ⟨N, hN⟩ := exists_source_window_tail
    (G.subsequence_strictMono.tendsto_atTop.eventually (htime a b hbT))
  let W := G.window F (ha.trans hb) hbT.le N hN
  apply W.ball_volume_lower_bound_of_eventually_static_noncollapse
    (htw (mem_singleton t)) (hcomplete t ht) x hr κ ?_ hcurv
  intro ρ hρ _
  have hevent := (G.subsequence_strictMono.tendsto_atTop.comp
    (tendsto_add_atTop_nat N)).eventually (hsource t ht)
  filter_upwards [hevent] with k hk
  exact hk _ ρ hρ

end PoincareConjecture.AncientPointedGeometricConvergence
