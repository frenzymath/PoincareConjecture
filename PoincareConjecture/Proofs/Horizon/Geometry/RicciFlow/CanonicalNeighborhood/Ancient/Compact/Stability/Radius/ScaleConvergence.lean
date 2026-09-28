import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Radius.Continuity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Scalar.Terminal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

section IntrinsicRadius

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T3Space M] [ConnectedSpace M]

theorem scalarCoreRadius_le_max_distance_scale (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (hc : MetricComplete g)
    (hpos : ∀ x : M, 0 < D.scalarCurvature x) (p x : M) :
    scalarCoreRadius g D hc hpos p ≤
      max (g.edist p x).toReal (Real.sqrt (D.scalarCurvature x))⁻¹ := by
  let : MetricSpace M := g.toMetricSpace
  let : ProperSpace M := g.properSpace_toMetricSpace hc
  have hs := scalarCoreRadius_spec g D hc hpos p
  apply CompactKappaCoreRadius.radius_le_max_distance_scale
    D.continuous_scalarCurvature hpos p hs.1
  simpa only [scalarCurvatureSupOn, ← Set.image_eq_range, ← g.toMetricSpace_ball] using hs.2

theorem exists_scalarCoreRadius_witness (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (hc : MetricComplete g)
    (hpos : ∀ x : M, 0 < D.scalarCurvature x) (p : M) :
    ∃ x : M, (g.edist p x).toReal ≤ scalarCoreRadius g D hc hpos p ∧
      (Real.sqrt (D.scalarCurvature x))⁻¹ = scalarCoreRadius g D hc hpos p := by
  let : MetricSpace M := g.toMetricSpace
  let : ProperSpace M := g.properSpace_toMetricSpace hc
  obtain ⟨r, hr, heq, x, hx, hscale⟩ :=
    CompactKappaCoreRadius.exists_sup_ball_inv_sq_witness
      (fun x _ hr ↦ CompactKappaCoreRadius.closure_ball_eq_of_approximate_split
        (fun x y _ _ hr hε ↦ g.approximate_split_toMetricSpace x y hr hε) x hr)
      D.scalarCurvature D.continuous_scalarCurvature hpos p
  have hradius : r = scalarCoreRadius g D hc hpos p :=
    eq_scalarCoreRadius_of_spec g D hc hpos p hr (by
      simpa only [scalarCurvatureSupOn, ← Set.image_eq_range, ← g.toMetricSpace_ball] using heq)
  rw [hradius] at hx hscale
  exact ⟨x, by simpa only [Metric.mem_closedBall, dist_comm,
    RiemannianMetric.toMetricSpace_dist] using hx, hscale⟩

end IntrinsicRadius

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

namespace M23TerminalMetricConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}

theorem tendstoUniformlyOn_terminal_scalarScale
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (t : ℝ), t ≤ 0 → ∀ x ∈ G.exhaustion k,
      ((e k).toFun (t, x)).2 = ((e k).toFun (0, x)).2)
    (hpos : ∀ x, 0 < (G.limit.flow.flow.connection 0).scalarCurvature x)
    {K : Set G.limit.carrier.carrier} (hK : IsCompact K) :
    TendstoUniformlyOn (fun k x ↦
      (Real.sqrt (((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
        ((e k).toFun (0, x)).2))⁻¹)
      (fun x ↦ (Real.sqrt ((G.limit.flow.flow.connection 0).scalarCurvature x))⁻¹)
      atTop K := by
  classical
  have hcont : Continuous (fun x ↦
      (Real.sqrt ((G.limit.flow.flow.connection 0).scalarCurvature x))⁻¹) :=
    (Real.continuous_sqrt.comp (G.limit.flow.flow.connection 0).continuous_scalarCurvature).inv₀
      (fun x ↦ (Real.sqrt_pos.mpr (hpos x)).ne')
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro δ hδ
  have hlocal (p : G.limit.carrier.carrier) :
      ∃ U ∈ 𝓝 p, ∀ᶠ k in atTop, ∀ x ∈ U,
        dist (Real.sqrt ((G.limit.flow.flow.connection 0).scalarCurvature x))⁻¹
          (Real.sqrt (((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
            ((e k).toFun (0, x)).2))⁻¹ < δ := by
    have hlim := (hcont.continuousAt.tendsto (x := p)).comp
      (tendsto_snd : Tendsto (Prod.snd : ℕ × G.limit.carrier.carrier → _)
        (atTop ×ˢ 𝓝 p) (𝓝 p))
    have hsource := ((hconv.tendsto_terminal_scalarCurvature_prod hfixed p).sqrt).inv₀
      (Real.sqrt_pos.mpr (hpos p)).ne'
    have herr := (hlim.dist hsource).eventually
      (gt_mem_nhds (by simpa only [dist_self] using hδ))
    obtain ⟨P, hP, Q, hQ, hPQ⟩ := eventually_prod_iff.mp herr
    exact ⟨{x | Q x}, hQ, hP.mono (fun k hk x hx ↦ hPQ hk hx)⟩
  choose U hU hbound using hlocal
  obtain ⟨s, _, hs⟩ := hK.elim_nhds_subcover U (fun x _ ↦ hU x)
  filter_upwards [s.eventually_all.mpr (fun x _ ↦ hbound x)] with k hk x hx
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hs hx)
  exact hk p hp x hxp

end M23TerminalMetricConvergence

end PoincareConjecture
