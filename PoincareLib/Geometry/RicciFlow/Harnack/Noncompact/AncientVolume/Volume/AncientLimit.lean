import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Volume.LimitLowerBound
import PoincareLib.Geometry.RicciFlow.Compactness.Ancient.Restriction

/-!
# Volume lower bounds for the constructed ancient pointed limit

Restricting one ancient geometric limit to a finite window preserves its
metric and spatial carrier. The fixed-window volume theorem therefore
transfers source lower bounds to the same ancient flow, without another
compactness selection. This is the volume step in Kleiner--Lott,
Proposition 41.13, printed p. 2678.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.AncientPointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t3Space

/-- The actual ancient limit retains every eventual source volume lower
bound at the base time, using its own normalized Riemannian volume. -/
theorem ball_volume_lower_bound_of_ancient_source_bounds
    {n : ℕ} {C : ℕ → FlowCarrier.{0} n} {J : ℕ → Set ℝ}
    (F : ∀ k, RicciFlow n (C k).carrier (J k)) {p : ∀ k, (C k).carrier} {T : ℝ}
    (G : AncientPointedGeometricConvergence C (fun k => (F k).metric) p T)
    (hT : 0 < T)
    (htime : ∀ a b : ℝ, b < T → ∀ᶠ k in atTop, Icc a b ⊆ J k)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))
    (v : ℝ)
    (hvolume : ∀ r : ℝ, 0 < r → ∀ᶠ k in atTop,
      ENNReal.ofReal (v * r ^ n) ≤
        ((F k).metric 0).volumeMeasure (((F k).metric 0).ball (p k) r)) :
    ∀ r : ℝ, 0 < r → ENNReal.ofReal (v * r ^ n) ≤
      (G.limitFlow.metric 0).volumeMeasure ((G.limitFlow.metric 0).ball G.base r) := by
  obtain ⟨a, b, ha, hb, hbT, _⟩ := exists_ancient_window_of_isCompact hT
    isCompact_singleton (singleton_subset_iff.mpr hT)
  obtain ⟨N, hN⟩ := exists_source_window_tail
    (G.subsequence_strictMono.tendsto_atTop.eventually (htime a b hbT))
  let W := G.window F (ha.trans hb) hbT.le N hN
  apply W.ball_volume_lower_bound_of_metricComplete_zero ⟨ha, hb⟩ hcomplete v
  intro r hr
  exact (G.subsequence_strictMono.tendsto_atTop.comp (tendsto_add_atTop_nat N)).eventually
    (hvolume r hr)

end PoincareMT.AncientPointedGeometricConvergence
