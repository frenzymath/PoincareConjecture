import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Radius.Convergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Radius.ClosedCore
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Metric.CompactCarrier
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.SpatialEmbedding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

theorem scalarCoreRadius_eq_of_connection
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T3Space M] [ConnectedSpace M]
    (g : RiemannianMetric 3 M) (D E : LeviCivitaData g) (hc : MetricComplete g)
    (hD : ∀ x, 0 < D.scalarCurvature x) (hE : ∀ x, 0 < E.scalarCurvature x) :
    scalarCoreRadius g D hc hD = scalarCoreRadius g E hc hE := by
  funext p
  have hs := scalarCoreRadius_spec g D hc hD p
  apply eq_scalarCoreRadius_of_spec g E hc hE p hs.1
  have heq : D.scalarCurvature = E.scalarCurvature := funext (D.scalarCurvature_eq E)
  simpa only [scalarCurvatureSupOn, heq] using hs.2

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

namespace M23TerminalMetricConvergence

theorem exists_cap_core_ball_transport_threshold :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
        {G : M23InteriorConvergence S}
        {e : ∀ j, NormalizedKappaSpacetimeEmbedding
          (source := S.term (G.subsequence j)) (target := G.limit)
          (Iic 0 ×ˢ G.exhaustion j)},
        M23TerminalMetricConvergence G e →
        (∀ k (t : ℝ), t ≤ 0 → ∀ x ∈ G.exhaustion k,
          ((e k).toFun (t, x)).2 = ((e k).toFun (0, x)).2) →
        ∀ (_hlimit : ∀ x, 0 < (G.limit.flow.flow.connection 0).scalarCurvature x)
          (hsource : ∀ k x,
            0 < ((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature x)
          (A : CapCertificate (G.limit.flow.flow.metric 0)),
          A.epsilon ≤ epsilon₀ →
          ∀ᶠ k in atTop, ∀ p ∈ A.closed_core,
            closure (((S.term (G.subsequence k)).flow.flow.metric 0).ball
              ((e k).toFun (0, p)).2
              (scalarCoreRadius ((S.term (G.subsequence k)).flow.flow.metric 0)
                ((S.term (G.subsequence k)).flow.flow.connection 0)
                ((S.term (G.subsequence k)).flow.complete 0 le_rfl) (hsource k)
                ((e k).toFun (0, p)).2)) ⊆
              (fun x ↦ ((e k).toFun (0, x)).2) '' A.carrier := by
  obtain ⟨epsilon₀, hepsilon₀, hsmall, hbuffer⟩ :=
    CapCertificate.exists_uniform_closedCore_ball_buffer_threshold.{0}
  refine ⟨epsilon₀, hepsilon₀, hsmall, ?_⟩
  intro kappa S G e hconv hfixed hlimit hsource A hepsilon
  let g := G.limit.flow.flow.metric 0
  let D := G.limit.flow.flow.connection 0
  let hc := G.limit.flow.complete 0 le_rfl
  let r := scalarCoreRadius g D hc hlimit
  have hr (p : G.limit.carrier.carrier) : 0 < r p :=
    (scalarCoreRadius_spec g D hc hlimit p).1
  have hApos (x : G.limit.carrier.carrier) : 0 < A.connection.scalarCurvature x := by
    rw [A.connection.scalarCurvature_eq D]
    exact hlimit x
  obtain ⟨delta, hdelta, hinside⟩ := hbuffer A hc hApos hepsilon
  have hrA : scalarCoreRadius g A.connection hc hApos = r :=
    scalarCoreRadius_eq_of_connection g A.connection D hc hApos hlimit
  have hinside' (p : G.limit.carrier.carrier) (hp : p ∈ A.closed_core) :
      closure (g.ball p ((1 + delta) * r p)) ⊆ A.carrier := by
    rw [← hrA]
    exact hinside p hp
  let C := Real.sqrt (1 + delta / 2)
  have hCnonneg : 0 ≤ C := Real.sqrt_nonneg _
  have hCsq : C ^ 2 = 1 + delta / 2 := Real.sq_sqrt (by linarith)
  have hC : 1 < C := by nlinarith
  have hCpos : 0 < C := zero_lt_one.trans hC
  have hCbuffer : C ^ 2 < 1 + delta := by rw [hCsq]; linarith
  have hcompact := A.isCompact_closure_carrier hc
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hcompact
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  filter_upwards [eventually_ge_atTop j,
    hconv.eventually_tangentNorm_bounds_on_compact hcompact hC,
    hconv.eventually_scalarCoreRadius_le_mul_on_compact hfixed hlimit hsource
      A.closed_core_compact hC] with k hk hmetric hradius p hp
  let E := (e k).spatialHomeomorph (mem_Iic.mpr le_rfl) (G.exhaustion_open k)
  let gk := (S.term (G.subsequence k)).flow.flow.metric 0
  let Dk := (S.term (G.subsequence k)).flow.flow.connection 0
  let rk := scalarCoreRadius gk Dk
    ((S.term (G.subsequence k)).flow.complete 0 le_rfl) (hsource k) (E p)
  have hrk : 0 < rk := (scalarCoreRadius_spec gk Dk
    ((S.term (G.subsequence k)).flow.complete 0 le_rfl) (hsource k) (E p)).1
  let R := (1 + delta) * r p
  have hR : 0 < R := mul_pos (by linarith) (hr p)
  have hCrk : C * rk < R := by
    have hmul := mul_le_mul_of_nonneg_left (hradius p hp) hCpos.le
    have hlt := mul_lt_mul_of_pos_right hCbuffer (hr p)
    change C * rk ≤ C * (C * r p) at hmul
    dsimp only [R]
    nlinarith
  have hrdiv : rk < R / C := (lt_div_iff₀ hCpos).mpr (by simpa only [mul_comm] using hCrk)
  let s := (rk + R / C) / 2
  have hrks : rk < s := by dsimp [s]; linarith
  have hCs : C * s < R := by
    have hs : s < R / C := by dsimp [s]; linarith
    simpa only [mul_comm] using (lt_div_iff₀ hCpos).mp hs
  have hsourceA : closure A.carrier ⊆ E.source := hj.trans (hmono hk)
  have hsourceBall : closure (g.ball p R) ⊆ E.source :=
    (hinside' p hp).trans (subset_closure.trans hsourceA)
  have hE : ContMDiffOn (𝓡 3) (𝓡 3) 1 E E.source :=
    ((e k).spatialHomeomorph_contMDiffOn (mem_Iic.mpr le_rfl)
      (G.exhaustion_open k)).of_le (by simp)
  have hEi : ContMDiffOn (𝓡 3) (𝓡 3) 1 E.symm E.target :=
    ((e k).spatialHomeomorph_symm_contMDiffOn (mem_Iic.mpr le_rfl)
      (G.exhaustion_open k)).of_le (by simp)
  have hEd : E.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨hE.mdifferentiableOn one_ne_zero, hEi.mdifferentiableOn one_ne_zero⟩
  have hinverse := g.inverse_tangentNorm_le_of_le gk E hEd hsourceBall
    (fun z hz v ↦ (hmetric z (subset_closure (hinside' p hp hz)) v).2)
  have hcoverage := g.ball_subset_image_ball_of_inverse_tangentNorm_le gk E p hR hCpos hCs
    (g.isCompact_closure_ball_of_metricComplete hc p R) hsourceBall
    (fun z hz ↦ hEi.contMDiffAt (E.open_target.mem_nhds hz)) hinverse
  have hclosed : closure (gk.ball (E p) rk) ⊆ gk.ball (E p) s := by
    let : MetricSpace (S.term (G.subsequence k)).carrier.carrier := gk.toMetricSpace
    rw [← gk.toMetricSpace_ball, ← gk.toMetricSpace_ball]
    exact Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball hrks)
  apply hclosed.trans (hcoverage.trans (image_mono ?_))
  intro z hz
  apply hinside' p hp
  exact subset_closure (hz.trans_le (ENNReal.ofReal_le_ofReal hCs.le))

end M23TerminalMetricConvergence

end PoincareConjecture
