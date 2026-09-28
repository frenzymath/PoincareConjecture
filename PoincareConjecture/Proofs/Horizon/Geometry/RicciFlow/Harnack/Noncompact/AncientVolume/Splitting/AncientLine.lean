import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.CompleteCoverage
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Restriction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.AncientPointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

theorem exists_isometric_line_of_source_arcs
    {n : ℕ} {C : ℕ → FlowCarrier.{0} n} {J : ℕ → Set ℝ}
    (F : ∀ k, RicciFlow n (C k).carrier (J k)) {p : ∀ k, (C k).carrier} {T : ℝ}
    (G : AncientPointedGeometricConvergence C (fun k => (F k).metric) p T)
    (hT : 0 < T)
    (htime : ∀ a b : ℝ, b < T → ∀ᶠ k in atTop, Icc a b ⊆ J k)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))
    (arc : ∀ k, ℝ → (C k).carrier) (hbase : ∀ k, arc k 0 = p k)
    (hdist : ∀ s t : ℝ, Tendsto (fun k =>
      (((F k).metric 0).edist (arc k s) (arc k t)).toReal) atTop (𝓝 |s - t|)) :
    letI := G.limitCarrier.metricSpaceOf (G.limitFlow.metric 0)
    ∃ gamma : ℝ → G.limitCarrier.carrier, Isometry gamma ∧ gamma 0 = G.base := by
  obtain ⟨a, b, ha, hb, hbT, _⟩ := exists_ancient_window_of_isCompact hT
    isCompact_singleton (singleton_subset_iff.mpr hT)
  obtain ⟨N, hN⟩ := exists_source_window_tail
    (G.subsequence_strictMono.tendsto_atTop.eventually (htime a b hbT))
  let W := G.window F (ha.trans hb) hbT.le N hN
  have hcover := W.source_ball_coverage_of_metricComplete_zero ⟨ha, hb⟩ hcomplete
  obtain ⟨gamma, hi, hzero, _⟩ := W.exists_isometric_line_of_source_arcs
    ⟨ha, hb⟩ hcover (fun k => arc (G.subsequence (k + N)))
    (fun k => hbase (G.subsequence (k + N)))
    (fun s t => (hdist s t).comp
      (G.subsequence_strictMono.tendsto_atTop.comp (tendsto_add_atTop_nat N)))
  exact ⟨gamma, hi, hzero⟩

end PoincareConjecture.AncientPointedGeometricConvergence
