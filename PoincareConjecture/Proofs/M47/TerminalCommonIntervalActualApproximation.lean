import PoincareConjecture.Proofs.M47.TerminalCommonIntervalOriginalApproximation
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalActualCross
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalCompactCapture









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v w

namespace PoincareConjecture.M47



theorem terminalCommonInterval_metric_approximation
    {X : ℕ → Type u} [∀ n, MetricSpace (X n)]
    [∀ n, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (X n)]
    [∀ n, IsManifold (𝓡 3) ∞ (X n)]
    (h : ∀ n, RiemannianMetric 3 (X n))
    (hactual : ∀ n (x y : X n), edist x y = (h n).edist x y)
    {Z : Type v} (K : Set Z) (a b : ∀ n, Z → X n)
    (hconv : TendstoUniformlyOn (fun n z => dist (b n z) (a n z))
      (fun _ => (0 : ℝ)) atTop K) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop, ∀ z ∈ K,
      (h n).edist (a n z) (b n z) < ENNReal.ofReal eta := by
  intro eta heta
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv eta heta] with n hn z hz
  rw [← hactual, edist_lt_ofReal, dist_comm]
  simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg dist_nonneg] using hn z hz

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance actualApproximationTopology :
    TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
private local instance actualApproximationT3 : T3Space G.limit.carrier.carrier :=
  G.limit.carrier.t3Space
private local instance actualApproximationCharts :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance actualApproximationManifold :
    IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold
private local instance actualApproximationConnected : ConnectedSpace G.limit.carrier.carrier :=
  G.limit.connectedSpace



theorem terminalCommonInterval_actual_original_approximation
    {M : Type v} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (hg : MetricComplete g) (p : M)
    (e : ∀ n, OpenPartialHomeomorph M
      ((V.flow (G.subsequence n)).slice (V.base (G.subsequence n)).1).carrier)
    (he : ∀ n, ContMDiffOn (𝓡 3) (𝓡 3) 1 (e n) (e n).source)
    (hbase : ∀ n, e n p = (V.base (G.subsequence n)).2)
    (hE : terminalCommonInterval_compactTangentControl g
      (fun n => M13.scaleSmoothMetric
        ((V.flow (G.subsequence n)).metric (V.base (G.subsequence n)).1)
        (V.scale (G.subsequence n)) (V.base_scalar_pos (G.subsequence n))) e)
    (rho : ℕ → ℕ) (hrho : StrictMono rho) (I : M → G.limit.carrier.carrier)
    (hconv : letI := g.toMetricSpace
      letI : MetricSpace G.limit.carrier.carrier := (G.limit.flow.metric 0).toMetricSpace
      letI : MetricSpace G.limit.sliceCarrier.carrier := (G.limit.flow.metric 0).toMetricSpace
      ∀ j : ℕ, TendstoUniformlyOn
        (fun n x => ((e (rho n)).trans
          (terminalCommonInterval_m30TerminalMap G (rho n)).symm x : G.limit.carrier.carrier))
        I atTop (Metric.closedBall p (j + 1)))
    {Z : Type w} (iota : Z → M) (K : Set Z) (hK : IsCompact (iota '' K))
    (a : ∀ n, Z → ((V.flow (G.subsequence n)).slice (V.base (G.subsequence n)).1).carrier)
    (happrox : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop, ∀ z ∈ K,
      RiemannianMetric.edist (M13.scaleSmoothMetric
        ((V.flow (G.subsequence n)).metric (V.base (G.subsequence n)).1)
        (V.scale (G.subsequence n)) (V.base_scalar_pos (G.subsequence n)))
          (a n z) (e n (iota z)) < ENNReal.ofReal eta) :
    letI : MetricSpace G.limit.carrier.carrier := (G.limit.flow.metric 0).toMetricSpace
    letI : MetricSpace G.limit.sliceCarrier.carrier := (G.limit.flow.metric 0).toMetricSpace
    ∃ R : ℝ, 0 < R ∧
      (∀ᶠ n in atTop, ∀ z ∈ K,
        a (rho n) z ∈ (terminalCommonInterval_m30TerminalMap G (rho n)).target ∧
          (terminalCommonInterval_m30TerminalMap G (rho n)).symm (a (rho n) z) ∈
            (G.limit.flow.metric 0).ball G.limit.base R) ∧
      TendstoUniformlyOn
        (fun n z => ((terminalCommonInterval_m30TerminalMap G (rho n)).symm
          (a (rho n) z) : G.limit.carrier.carrier))
        (I ∘ iota) atTop K := by
  let := g.toMetricSpace
  let k := G.limit.flow.metric 0
  let : MetricSpace G.limit.carrier.carrier := k.toMetricSpace
  let : MetricSpace G.limit.sliceCarrier.carrier := k.toMetricSpace
  let f (n : ℕ) : OpenPartialHomeomorph G.limit.carrier.carrier
      ((V.flow (G.subsequence n)).slice (V.base (G.subsequence n)).1).carrier :=
    terminalCommonInterval_m30TerminalMap G n
  let h (n : ℕ) : RiemannianMetric 3
      ((V.flow (G.subsequence n)).slice (V.base (G.subsequence n)).1).carrier :=
    M13.scaleSmoothMetric ((V.flow (G.subsequence n)).metric (V.base (G.subsequence n)).1)
      (V.scale (G.subsequence n)) (V.base_scalar_pos (G.subsequence n))
  have hE' : terminalCommonInterval_compactTangentControl g
      (fun n => h (rho n)) (fun n => e (rho n)) :=
    fun _ hL _ hl hlt => hrho.tendsto_atTop.eventually (hE _ hL _ hl hlt)
  have hF' : terminalCommonInterval_compactTangentControl k
      (fun n => h (rho n)) (fun n => f (rho n)) :=
    fun _ hL _ hl hlt => hrho.tendsto_atTop.eventually
      (terminalCommonInterval_m30_terminal_tangent G hL hl hlt)
  have hcross : TendstoUniformlyOn
      (fun n z => (f (rho n)).symm (e (rho n) (iota z))) (I ∘ iota) atTop K := by
    have hcompact := terminalCommonInterval_uniform_on_compacts_of_balls p hconv hK
    exact (hcompact.comp iota).mono (fun z hz => mem_image_of_mem iota hz)
  exact terminalCommonInterval_original_approximation g k (fun n => h (rho n)) hg
    (G.limit.complete 0 G.limit.zero_mem) (fun n => e (rho n)) (fun n => f (rho n))
    (fun n => he (rho n))
    (fun n => (terminalCommonInterval_m30_terminal_source G (rho n)).2.1.of_le (by simp))
    (fun n => (terminalCommonInterval_m30_terminal_source G (rho n)).2.2.of_le (by simp))
    p G.limit.base (fun n => (hbase (rho n)).trans
      (terminalCommonInterval_m30_terminal_base G (rho n)).symm)
    hE' hF' iota K hK (fun n => a (rho n))
    (fun eta heta => hrho.tendsto_atTop.eventually (happrox eta heta)) I hcross

end PoincareConjecture.M47
