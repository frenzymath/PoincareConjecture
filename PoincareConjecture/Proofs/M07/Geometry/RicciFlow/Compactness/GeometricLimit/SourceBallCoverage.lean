import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Embedding.BallTransfer
import PoincareConjecture.Proofs.M07.Topology.MetricSpace.Completeness

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.PointedGeometricConvergence

variable {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}

theorem zeroBall_subset_exhaustion_of_source_ball_coverage
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    {A : ℝ} {j : ℕ}
    (hcover : ∀ᶠ k in atTop,
      (S.flow (G.subsequence k)).zeroBall (2 * A) ⊆
        (fun x => ((G.embedding k).toFun (0, x)).2) '' G.exhaustion j) :
    G.limitFlow.zeroBall A ⊆ G.exhaustion j := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  intro x hx
  have hxball : x ∈ G.limitFlow.ballAt 0 A := hx
  obtain ⟨jx, hjx⟩ := G.exists_exhaustion_superset (K := {x}) isCompact_singleton
  have hxstage : x ∈ G.exhaustion jx := hjx (mem_singleton x)
  obtain ⟨k, hkcover, hkball, hkj, hkjx⟩ :=
    (hcover.and ((G.eventually_mem_ballAt hT hT hxball).and
      ((eventually_ge_atTop j).and (eventually_ge_atTop jx)))).exists
  obtain ⟨y, hy, heq⟩ := hkcover hkball
  have heq' : (G.embedding k).toFun (0, y) = (G.embedding k).toFun (0, x) := by
    apply Prod.ext
    · simp only [(G.embedding k).time_preserving]
    · exact heq
  have hyx : y = x := congrArg Prod.snd ((G.embedding k).injective_on (x₁ := (0, y))
    (x₂ := (0, x))
    ⟨hT, G.exhaustion_monotone hkj hy⟩
    ⟨hT, G.exhaustion_monotone hkjx hxstage⟩ heq')
  simpa only [hyx] using hy

theorem isCompact_closure_zeroBall_of_source_ball_coverage
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    (hcover : ∀ A : ℝ, 0 < A → ∃ j : ℕ, ∀ᶠ k in atTop,
      (S.flow (G.subsequence k)).zeroBall A ⊆
        (fun x => ((G.embedding k).toFun (0, x)).2) '' G.exhaustion j)
    (A : ℝ) (hA : 0 < A) :
    letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
    IsCompact (closure (G.limitFlow.zeroBall A)) := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  obtain ⟨j, hj⟩ := hcover (2 * A) (by positivity)
  exact (G.exhaustion_compactClosure j).of_isClosed_subset isClosed_closure
    (closure_mono (G.zeroBall_subset_exhaustion_of_source_ball_coverage hT hj))

set_option backward.isDefEq.respectTransparency false in

theorem metricComplete_zero_of_source_ball_coverage
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    (hcover : ∀ A : ℝ, 0 < A → ∃ j : ℕ, ∀ᶠ k in atTop,
      (S.flow (G.subsequence k)).zeroBall A ⊆
        (fun x => ((G.embedding k).toFun (0, x)).2) '' G.exhaustion j) :
    G.limitCarrier.metricComplete (G.limitFlow.metricAt 0) := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : EMetricSpace G.limitCarrier.carrier :=
    G.limitCarrier.metricEMetricSpace (G.limitFlow.metricAt 0)
  let : PreconnectedSpace G.limitCarrier.carrier :=
    FlowCarrier.preconnected_metricEMetricSpace G.limitCarrier (G.limitFlow.metricAt 0)
  change CompleteSpace G.limitCarrier.carrier
  apply EMetric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff'.mp hu 1 zero_lt_one
  let d := edist (u N) G.limitFlow.base
  have hd : d ≠ ⊤ := Poincare.edist_ne_top_of_preconnected _ _
  let R : ℝ := d.toReal + 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hcompact := G.isCompact_closure_zeroBall_of_source_ball_coverage hT hcover R hR
  have htail : ∀ᶠ k in atTop, u k ∈ closure (G.limitFlow.zeroBall R) := by
    filter_upwards [eventually_ge_atTop N] with k hk
    apply subset_closure
    change edist G.limitFlow.base (u k) < ENNReal.ofReal R
    rw [edist_comm]
    calc
      edist (u k) G.limitFlow.base ≤ edist (u k) (u N) + d := edist_triangle _ _ _
      _ < 1 + d := ENNReal.add_lt_add_right hd (hN k hk)
      _ ≤ ENNReal.ofReal R := by
        dsimp [R]
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num),
          ENNReal.ofReal_toReal hd]
        norm_num
        simpa only [add_comm d] using
          add_le_add_left (by norm_num : (1 : ℝ≥0∞) ≤ 2) d
  obtain ⟨x, _, hx⟩ := hcompact.isComplete (map u atTop) hu
    (le_principal_iff.mpr htail)
  exact ⟨x, hx⟩

end PoincareConjecture.PointedGeometricConvergence
