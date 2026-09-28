import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Scalar.Germs
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Scalar.Jets
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace
  normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

namespace M23TerminalMetricConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}



theorem tendsto_terminal_coordinate_scalarCurvature_prod
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (t : ℝ), t ≤ 0 → ∀ x ∈ G.exhaustion k,
      ((e k).toFun (t, x)).2 = ((e k).toFun (0, x)).2)
    (q : G.limit.carrier.carrier) {p : EuclideanSpace ℝ (Fin 3)}
    (hp : p ∈ (extChartAt (𝓡 3) q).target) :
    Tendsto (fun z : ℕ × EuclideanSpace ℝ (Fin 3) ↦
      ((S.term (G.subsequence z.1)).flow.flow.connection 0).scalarCurvature
        ((e z.1).toFun (0, (extChartAt (𝓡 3) q).symm z.2)).2)
      (atTop ×ˢ 𝓝 p) (𝓝 ((G.limit.flow.flow.connection 0).scalarCurvature
        ((extChartAt (𝓡 3) q).symm p))) := by
  let c := extChartAt (𝓡 3) q
  obtain ⟨g, D, V, hVo, hpV, _, heq⟩ := G.limit.carrier.exists_local_coordinate_realization
    (G.limit.flow.flow.metric 0) q 0 p hp
  have hg := Filter.Eventually.mono (hVo.mem_nhds hpV) heq
  let φ := fun (z : ℕ × EuclideanSpace ℝ (Fin 3)) y ↦ ((e z.1).toFun (0, c.symm y)).2
  have hφ : ∀ᶠ z : ℕ × EuclideanSpace ℝ (Fin 3) in atTop ×ˢ 𝓝 p,
      ∀ᶠ y in 𝓝 z.2, ContMDiffAt (𝓡 3) (𝓡 3) ∞ (φ z) y ∧
        Function.Injective (mfderiv (𝓡 3) (𝓡 3) (φ z) y) := by
    filter_upwards [eventually_terminal_chart_domain (G := G) q hp] with z hz
    let W := c.target ∩ c.symm ⁻¹' G.exhaustion z.1
    have hW : IsOpen W := (continuousOn_extChartAt_symm q).isOpen_inter_preimage
      (isOpen_extChartAt_target q) (G.exhaustion_open z.1)
    filter_upwards [hW.mem_nhds hz] with y hy
    exact (e z.1).terminal_chart_map_regular (G.exhaustion_open z.1) q hy.1 hy.2
  have hscalar := LeviCivitaData.tendsto_scalarCurvature_of_moving_scalar_pullback_jets
    (fun z : ℕ × EuclideanSpace ℝ (Fin 3) ↦ (S.term (G.subsequence z.1)).flow.flow.connection 0)
    φ D (fun z ↦ z.2) p hφ (by
      intro r _ a b
      rw [G.limit.carrier.iteratedFDeriv_coordinateCoefficient_eq_of_eventuallyEq
        q _ 0 p g hg r a b]
      exact hconv.tendsto_terminal_spatialJet_prod hfixed q hp r a b)
  rw [G.limit.carrier.scalarCurvature_eq_of_coordinate_germ
    (G.limit.flow.flow.metric 0) (G.limit.flow.flow.connection 0) q 0 p hp g D hg] at hscalar
  exact hscalar



theorem tendsto_terminal_scalarCurvature_prod
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (t : ℝ), t ≤ 0 → ∀ x ∈ G.exhaustion k,
      ((e k).toFun (t, x)).2 = ((e k).toFun (0, x)).2)
    (p : G.limit.carrier.carrier) :
    Tendsto (fun z : ℕ × G.limit.carrier.carrier ↦
      ((S.term (G.subsequence z.1)).flow.flow.connection 0).scalarCurvature
        ((e z.1).toFun (0, z.2)).2)
      (atTop ×ˢ 𝓝 p) (𝓝 ((G.limit.flow.flow.connection 0).scalarCurvature p)) := by
  let c := extChartAt (𝓡 3) p
  have hp : p ∈ c.source := mem_extChartAt_source p
  have hn := (hconv.tendsto_terminal_coordinate_scalarCurvature_prod hfixed p
    (c.map_source hp)).comp (tendsto_id.prodMap (continuousAt_extChartAt p).tendsto)
  change Tendsto (fun z : ℕ × G.limit.carrier.carrier ↦
      ((S.term (G.subsequence z.1)).flow.flow.connection 0).scalarCurvature
        ((e z.1).toFun (0, c.symm (c z.2))).2)
      (atTop ×ˢ 𝓝 p) (𝓝 ((G.limit.flow.flow.connection 0).scalarCurvature (c.symm (c p)))) at hn
  rw [c.left_inv hp] at hn
  apply hn.congr'
  filter_upwards [tendsto_snd.eventually (extChartAt_source_mem_nhds (I := 𝓡 3) p)] with z hz
  rw [c.left_inv hz]



theorem tendstoUniformlyOn_terminal_scalarCurvature
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (t : ℝ), t ≤ 0 → ∀ x ∈ G.exhaustion k,
      ((e k).toFun (t, x)).2 = ((e k).toFun (0, x)).2)
    {A : Set G.limit.carrier.carrier} (hA : IsCompact A) :
    TendstoUniformlyOn (fun k x ↦
      ((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
        ((e k).toFun (0, x)).2)
      (G.limit.flow.flow.connection 0).scalarCurvature atTop A := by
  classical
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hlocal (p : G.limit.carrier.carrier) :
      ∃ U ∈ 𝓝 p, ∀ᶠ k in atTop, ∀ x ∈ U,
        dist ((G.limit.flow.flow.connection 0).scalarCurvature x)
          (((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
            ((e k).toFun (0, x)).2) < ε := by
    have hlim : Tendsto (fun z : ℕ × G.limit.carrier.carrier ↦
        (G.limit.flow.flow.connection 0).scalarCurvature z.2) (atTop ×ˢ 𝓝 p)
        (𝓝 ((G.limit.flow.flow.connection 0).scalarCurvature p)) :=
      ((G.limit.flow.flow.connection 0).continuous_scalarCurvature.continuousAt.tendsto
        (x := p)).comp tendsto_snd
    have hd := hlim.dist (hconv.tendsto_terminal_scalarCurvature_prod hfixed p)
    have herr := hd.eventually (gt_mem_nhds (by simpa only [dist_self] using hε))
    obtain ⟨P, hP, Q, hQ, hPQ⟩ := eventually_prod_iff.mp herr
    exact ⟨{x | Q x}, hQ, hP.mono (fun k hk x hx ↦ hPQ hk hx)⟩
  choose U hU hbound using hlocal
  obtain ⟨s, _, hs⟩ := hA.elim_nhds_subcover U (fun x _ ↦ hU x)
  filter_upwards [s.eventually_all.mpr (fun x _ ↦ hbound x)] with k hk x hx
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hs hx)
  exact hk p hp x hxp

end M23TerminalMetricConvergence

end PoincareConjecture
