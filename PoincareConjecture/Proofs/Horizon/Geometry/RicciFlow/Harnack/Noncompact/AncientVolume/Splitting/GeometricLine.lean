import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.LimitTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.LineLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.OppositeSegments

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology Bundle ENNReal

namespace PoincareConjecture.PointedGeometricConvergence

variable {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}

theorem properSpace_zero_of_source_ball_coverage
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    (hcover : ∀ A : ℝ, 0 < A → ∃ j : ℕ, ∀ᶠ k in atTop,
      (S.flow (G.subsequence k)).zeroBall A ⊆
        (fun x => ((G.embedding k).toFun (0, x)).2) '' G.exhaustion j) :
    letI := G.limitCarrier.metricSpaceOf (G.limitFlow.metricAt 0)
    ProperSpace G.limitCarrier.carrier := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  let : MetricSpace G.limitCarrier.carrier :=
    G.limitCarrier.metricSpaceOf (G.limitFlow.metricAt 0)
  apply ProperSpace.of_seq_closedBall (x := G.limitFlow.base)
    (r := fun i : ℕ => (i : ℝ)) tendsto_natCast_atTop_atTop
  apply Eventually.of_forall
  intro i
  have hcompact := G.isCompact_closure_zeroBall_of_source_ball_coverage hT hcover
    ((i : ℝ) + 1) (by positivity)
  have hball : G.limitFlow.zeroBall ((i : ℝ) + 1) =
      Metric.ball G.limitFlow.base ((i : ℝ) + 1) :=
    (FlowCarrier.metricBall_eq_metricBallOf G.limitCarrier (G.limitFlow.metricAt 0)
      G.limitFlow.base ((i : ℝ) + 1)).symm
  rw [hball] at hcompact
  apply hcompact.of_isClosed_subset isClosed_closedBall
  exact (closedBall_subset_ball (by linarith : (i : ℝ) < i + 1)).trans subset_closure

theorem exists_isometric_line_of_source_arcs
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    (hcover : ∀ A : ℝ, 0 < A → ∃ j : ℕ, ∀ᶠ k in atTop,
      (S.flow (G.subsequence k)).zeroBall A ⊆
        (fun x => ((G.embedding k).toFun (0, x)).2) '' G.exhaustion j)
    (arc : ∀ k, ℝ → (S.carrier (G.subsequence k)).carrier)
    (hbase : ∀ k, arc k 0 = (S.flow (G.subsequence k)).base)
    (hdist : ∀ s t : ℝ, Tendsto (fun k =>
      (((S.carrier (G.subsequence k)).metricEMetricSpace
        ((S.flow (G.subsequence k)).metricAt 0)).edist (arc k s) (arc k t)).toReal)
      atTop (𝓝 |s - t|)) :
    letI := G.limitCarrier.metricSpaceOf (G.limitFlow.metricAt 0)
    ∃ gamma : ℝ → G.limitCarrier.carrier,
      Isometry gamma ∧ gamma 0 = G.limitFlow.base ∧
      ∀ t : ℝ, Tendsto (fun k => ((G.embedding k).inverse (0, arc k t)).2)
        (hyperfilter ℕ : Filter ℕ) (𝓝 (gamma t)) := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  let : MetricSpace G.limitCarrier.carrier :=
    G.limitCarrier.metricSpaceOf (G.limitFlow.metricAt 0)
  let : ProperSpace G.limitCarrier.carrier :=
    G.properSpace_zero_of_source_ball_coverage hT hcover
  let targetArc := fun k t => ((G.embedding k).inverse (0, arc k t)).2
  have hbounded (t : ℝ) {A : ℝ} (hA : |t| < A) :
      ∀ᶠ k in atTop, arc k t ∈ (S.flow (G.subsequence k)).zeroBall A := by
    have hd : Tendsto (fun k =>
        (((S.carrier (G.subsequence k)).metricEMetricSpace
          ((S.flow (G.subsequence k)).metricAt 0)).edist
            (S.flow (G.subsequence k)).base (arc k t)).toReal) atTop (𝓝 |t|) := by
      simpa only [hbase, zero_sub, abs_neg] using hdist 0 t
    filter_upwards [hd.eventually (eventually_lt_nhds hA)] with k hk
    let Q := S.carrier (G.subsequence k)
    let : TopologicalSpace Q.carrier := Q.topologicalSpace
    let : ChartedSpace (EuclideanSpace ℝ (Fin n)) Q.carrier := Q.chartedSpace
    let : IsManifold (𝓡 n) ∞ Q.carrier := Q.isManifold
    let : T3Space Q.carrier := Q.t3Space
    let : PreconnectedSpace Q.carrier := ⟨Q.connected.isPreconnected⟩
    let g := (S.flow (G.subsequence k)).metricAt 0
    change g.edist (S.flow (G.subsequence k)).base (arc k t) < ENNReal.ofReal A
    exact (ENNReal.lt_ofReal_iff_toReal_lt (g.edist_ne_top _ _)).mpr hk
  have htargetBase (k : ℕ) : targetArc k 0 = G.limitFlow.base := by
    have hfp : ((G.embedding k).toFun (0, G.limitFlow.base)).2 =
        (S.flow (G.subsequence k)).base := congrArg Prod.snd (G.base_preserving k)
    dsimp [targetArc]
    rw [hbase, ← hfp]
    exact (G.embedding k).spatialInverse_comp_spatialMap hT (G.base_in_exhaustion k)
  apply Poincare.AncientVolume.Splitting.exists_isometric_line_of_dist_tendsto htargetBase
  intro s t
  have hh := G.tendsto_inverse_dist_of_source_ball_coverage hT hcover
    (fun k => arc k s) (fun k => arc k t)
    (A := |s| + |t| + 1) (by positivity)
    (hbounded s (by linarith [abs_nonneg t]))
    (hbounded t (by linarith [abs_nonneg s])) (hdist s t)
  exact hh

theorem exists_isometric_line_of_opposite_segments
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    (hcover : ∀ A : ℝ, 0 < A → ∃ j : ℕ, ∀ᶠ k in atTop,
      (S.flow (G.subsequence k)).zeroBall A ⊆
        (fun x => ((G.embedding k).toFun (0, x)).2) '' G.exhaustion j)
    (minus plus : ∀ k, ℝ → (S.carrier (G.subsequence k)).carrier)
    (hminus0 : ∀ k, minus k 0 = (S.flow (G.subsequence k)).base)
    (hplus0 : ∀ k, plus k 0 = (S.flow (G.subsequence k)).base)
    {a b : ℕ → ℝ} (ha : Tendsto a atTop atTop) (hb : Tendsto b atTop atTop) :
    letI : ∀ k, MetricSpace (S.carrier (G.subsequence k)).carrier :=
      fun k => (S.carrier (G.subsequence k)).metricSpaceOf
        ((S.flow (G.subsequence k)).metricAt 0)
    (∀ k, ∀ s ∈ Icc (0 : ℝ) (a k), ∀ t ∈ Icc (0 : ℝ) (a k),
      dist (minus k s) (minus k t) = |s - t|) →
    (∀ k, ∀ s ∈ Icc (0 : ℝ) (b k), ∀ t ∈ Icc (0 : ℝ) (b k),
      dist (plus k s) (plus k t) = |s - t|) →
    Tendsto (fun k => Poincare.AncientVolume.Splitting.segmentComparisonCosine
      (minus k) (plus k) (a k) (b k)) atTop (𝓝 (-1)) →
    (∀ k, ∀ s ∈ Icc (0 : ℝ) (a k), ∀ t ∈ Icc (0 : ℝ) (b k),
      s ^ 2 + t ^ 2 - 2 * s * t *
        Poincare.AncientVolume.Splitting.segmentComparisonCosine
          (minus k) (plus k) (a k) (b k) ≤ dist (minus k s) (plus k t) ^ 2) →
    letI := G.limitCarrier.metricSpaceOf (G.limitFlow.metricAt 0)
    ∃ gamma : ℝ → G.limitCarrier.carrier,
      Isometry gamma ∧ gamma 0 = G.limitFlow.base := by
  let : ∀ k, MetricSpace (S.carrier (G.subsequence k)).carrier :=
    fun k => (S.carrier (G.subsequence k)).metricSpaceOf
      ((S.flow (G.subsequence k)).metricAt 0)
  intro hminus hplus hangle hcomparison
  obtain ⟨arc, hbase, _, _, hdist⟩ :=
    Poincare.AncientVolume.Splitting.exists_two_sided_arcs_of_minimizing_segments
      (fun k => (S.flow (G.subsequence k)).base) minus plus hminus0 hplus0
      hminus hplus ha hb hangle hcomparison
  obtain ⟨gamma, hi, h0, _⟩ := G.exists_isometric_line_of_source_arcs hT hcover arc hbase hdist
  exact ⟨gamma, hi, h0⟩

end PoincareConjecture.PointedGeometricConvergence
