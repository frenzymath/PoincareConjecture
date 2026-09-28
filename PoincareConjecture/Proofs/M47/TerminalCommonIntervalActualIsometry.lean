import PoincareConjecture.Proofs.M47.TerminalCommonIntervalGlobalIsometry
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalActualCross
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M47

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space
private local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold
private local instance : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace



theorem terminalCommonInterval_actual_terminal_isometry
    {M : Type u} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [PreconnectedSpace M]
    (g : RiemannianMetric 3 M) (hg : MetricComplete g) (p : M)
    (e : ∀ n, OpenPartialHomeomorph M
      ((V.flow (G.subsequence n)).slice (V.base (G.subsequence n)).1).carrier)
    (he : ∀ n, ContMDiffOn (𝓡 3) (𝓡 3) 1 (e n) (e n).source)
    (hei : ∀ n, ContMDiffOn (𝓡 3) (𝓡 3) 1 (e n).symm (e n).target)
    (hbase : ∀ n, e n p = (V.base (G.subsequence n)).2)
    (hE : terminalCommonInterval_compactTangentControl g
      (fun n => M13.scaleSmoothMetric
        ((V.flow (G.subsequence n)).metric (V.base (G.subsequence n)).1)
        (V.scale (G.subsequence n)) (V.base_scalar_pos (G.subsequence n))) e) :
    letI := g.toMetricSpace
    letI : MetricSpace G.limit.carrier.carrier := (G.limit.flow.metric 0).toMetricSpace
    let T : ℕ → OpenPartialHomeomorph M G.limit.carrier.carrier :=
      fun n => (e n).trans (terminalCommonInterval_m30TerminalMap G n).symm
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ d : M ≃ᵢ G.limit.carrier.carrier,
      d p = G.limit.base ∧
      (∀ j : ℕ, TendstoUniformlyOn (fun n => T (rho n)) d atTop
        (Metric.closedBall p (j + 1))) ∧
      (∀ j : ℕ, TendstoUniformlyOn (fun n => (T (rho n)).symm) d.symm atTop
        (Metric.closedBall G.limit.base (j + 1))) := by
  let k := G.limit.flow.metric 0
  let := g.toMetricSpace
  let : MetricSpace G.limit.carrier.carrier := k.toMetricSpace
  have : ProperSpace M := g.properSpace_toMetricSpace hg
  have : ProperSpace G.limit.carrier.carrier :=
    k.properSpace_toMetricSpace (G.limit.complete 0 G.limit.zero_mem)
  let T : ℕ → OpenPartialHomeomorph M G.limit.carrier.carrier :=
    fun n => (e n).trans (terminalCommonInterval_m30TerminalMap G n).symm
  apply terminalCommonInterval_isometry_of_ball_control p G.limit.base T
  intro R hR lambda hlambda hlambda_lt
  filter_upwards [terminalCommonInterval_actual_cross_control G g hg p e he hei
    hbase hE hR hlambda hlambda_lt] with n hn
  obtain ⟨hsource, hmap, htarget, hmap', hforward, hreverse, hbase', hbase'', _⟩ := hn
  simpa only [T, g.toMetricSpace_closedBall p hR.le,
    k.toMetricSpace_closedBall G.limit.base hR.le, g.toMetricSpace_ball,
    k.toMetricSpace_ball, g.toMetricSpace_edist, k.toMetricSpace_edist,
    mem_ofPred_eq] using
    ⟨hsource, hmap, htarget, hmap', hforward, hreverse, hbase', hbase''⟩

end PoincareConjecture.M47
