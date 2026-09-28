import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeCriticalRadius
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeVolume
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.OpenMetricBalls
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.BoundaryCoverage











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}
  (H : CounterexampleNeckFamily E) (T : ∀ k, SourceTubeData (H.segment k))
  (Acrit : ℝ)


def tubeCriticalRegion (k : ℕ) : TopologicalSpace.Opens (T k).carrierOpen := by
  let g := H.tubeMetric T k
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (T k).carrierOpen → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : (T k).carrierOpen → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace (T k).carrierOpen :=
    EMetricSpace.ofRiemannianMetric (𝓡 3) (T k).carrierOpen
  refine ⟨g.ball (H.tubeBase T k) Acrit, ?_⟩
  change IsOpen {x | edist (H.tubeBase T k) x < ENNReal.ofReal Acrit}
  exact isOpen_lt (continuous_const.edist continuous_id) continuous_const


@[simp] theorem tubeCriticalRegion_coe (k : ℕ) :
    (H.tubeCriticalRegion T Acrit k : Set (T k).carrierOpen) =
      (H.tubeMetric T k).ball (H.tubeBase T k) Acrit := rfl


def tubeCriticalMetric (k : ℕ) : RiemannianMetric 3 (H.tubeCriticalRegion T Acrit k) :=
  intrinsicOpenMetric (H.tubeMetric T k) (H.tubeCriticalRegion T Acrit k)


def tubeCriticalBase (hA : 0 < Acrit) (k : ℕ) : H.tubeCriticalRegion T Acrit k := by
  refine ⟨H.tubeBase T k, ?_⟩
  change (H.tubeMetric T k).edist (H.tubeBase T k) (H.tubeBase T k) <
    ENNReal.ofReal Acrit
  simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
    ENNReal.ofReal_pos.mpr hA


@[simp] theorem tubeCriticalBase_val (hA : 0 < Acrit) (k : ℕ) :
    (H.tubeCriticalBase T Acrit hA k : (T k).carrierOpen) = H.tubeBase T k := rfl


theorem tubeCriticalRegion_connected (hA : 0 < Acrit) (k : ℕ) :
    ConnectedSpace (H.tubeCriticalRegion T Acrit k) := by
  apply Subtype.connectedSpace
  refine ⟨⟨H.tubeBase T k, (H.tubeCriticalBase T Acrit hA k).property⟩, ?_⟩
  exact (H.tubeMetric T k).isPreconnected_ball (H.tubeBase T k) Acrit



theorem tubeCritical_ball_eq_preimage (hA : 0 < Acrit) (k : ℕ)
    {r : ℝ} (hr : r ≤ Acrit) :
    (H.tubeCriticalMetric T Acrit k).ball (H.tubeCriticalBase T Acrit hA k) r =
      (Subtype.val : H.tubeCriticalRegion T Acrit k → (T k).carrierOpen) ⁻¹'
        (H.tubeMetric T k).ball (H.tubeBase T k) r := by
  apply intrinsicOpenMetric_ball_eq_preimage
  intro x hx
  exact hx.trans_le (ENNReal.ofReal_le_ofReal hr)



theorem tubeCritical_base_edist (hA : 0 < Acrit) (k : ℕ)
    (q : H.tubeCriticalRegion T Acrit k) :
    (H.tubeCriticalMetric T Acrit k).edist (H.tubeCriticalBase T Acrit hA k) q =
      (H.tubeMetric T k).edist (H.tubeBase T k) (q : (T k).carrierOpen) := by
  apply le_antisymm
  · by_contra hnot
    have hlt : (H.tubeMetric T k).edist (H.tubeBase T k) (q : (T k).carrierOpen) <
        (H.tubeCriticalMetric T Acrit k).edist (H.tubeCriticalBase T Acrit hA k) q :=
      lt_of_not_ge hnot
    have hq : (H.tubeMetric T k).edist (H.tubeBase T k) (q : (T k).carrierOpen) <
        ENNReal.ofReal Acrit := q.property
    obtain ⟨r, hdr, hr⟩ := exists_between (lt_min hlt hq)
    have hrA : r < ENNReal.ofReal Acrit := hr.trans_le (min_le_right _ _)
    have hrfinite : r ≠ ⊤ := ne_top_of_lt (hrA.trans_le le_top)
    have hrreal : r.toReal < Acrit := ENNReal.toReal_lt_of_lt_ofReal hrA
    have hqball : (q : (T k).carrierOpen) ∈
        (H.tubeMetric T k).ball (H.tubeBase T k) r.toReal := by
      change (H.tubeMetric T k).edist (H.tubeBase T k) (q : (T k).carrierOpen) <
        ENNReal.ofReal r.toReal
      simpa only [ENNReal.ofReal_toReal hrfinite] using hdr
    have hqsmall : q ∈ (H.tubeCriticalMetric T Acrit k).ball
        (H.tubeCriticalBase T Acrit hA k) r.toReal := by
      rw [H.tubeCritical_ball_eq_preimage T Acrit hA k hrreal.le]
      exact hqball
    change (H.tubeCriticalMetric T Acrit k).edist
      (H.tubeCriticalBase T Acrit hA k) q < ENNReal.ofReal r.toReal at hqsmall
    rw [ENNReal.ofReal_toReal hrfinite] at hqsmall
    exact (not_lt_of_ge (hr.trans_le (min_le_left _ _)).le) hqsmall
  · rw [tubeCriticalMetric, intrinsicOpenMetric_edist]
    exact RiemannianMetric.edist_le_intrinsicEDist (H.tubeMetric T k)
      (H.tubeCriticalRegion T Acrit k) (H.tubeBase T k) (q : (T k).carrierOpen)



theorem tubeCritical_base_regular (hA : 0 < Acrit)
    (hbase : (4 * max C 2)⁻¹ * epsilon⁻¹ / 8 ≤ Acrit) (k : ℕ) :
    H.tubeCriticalBase T Acrit hA k ∈ regularPoints (H.tubeCriticalMetric T Acrit k)
      (((4 * max C 2)⁻¹ * epsilon⁻¹ / 8) / 2) := by
  let : PreconnectedSpace (T k).carrierOpen := (T k).preconnected
  let rbase : ℝ := (4 * max C 2)⁻¹ * epsilon⁻¹ / 8
  have heps : 0 < epsilon :=
    (H.segment k).cover_epsilon ▸ (H.segment k).cover.epsilon_pos
  have hB : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right C 2)
  have hbasepos : 0 < rbase := by
    dsimp only [rbase]
    positivity
  intro r hr
  by_cases hr0 : r ≤ 0
  · have hempty : (H.tubeCriticalMetric T Acrit k).ball
        (H.tubeCriticalBase T Acrit hA k) r = ∅ := by
      ext q
      simp only [RiemannianMetric.ball, mem_ofPred_eq,
        ENNReal.ofReal_eq_zero.mpr hr0, not_lt_zero, mem_empty_iff_false]
    rw [hempty, closure_empty]
    exact isCompact_empty
  have hrr : r < rbase := hr.trans (half_lt_self hbasepos)
  have hrA : r < Acrit := hrr.trans_le hbase
  have hball : (H.tubeMetric T k).ball (H.tubeBase T k) r ⊆
      (H.tubeCriticalRegion T Acrit k : Set (T k).carrierOpen) := by
    intro q hq
    exact hq.trans_le (ENNReal.ofReal_le_ofReal hrA.le)
  have hclosed : IsClosed {q : (T k).carrierOpen |
      ((H.tubeMetric T k).edist (H.tubeBase T k) q).toReal ≤ r} :=
    isClosed_le ((H.tubeMetric T k).continuous_toReal_edist (H.tubeBase T k))
      continuous_const
  have hclosure_le : closure ((H.tubeMetric T k).ball (H.tubeBase T k) r) ⊆
      {q | ((H.tubeMetric T k).edist (H.tubeBase T k) q).toReal ≤ r} := by
    apply closure_minimal ?_ hclosed
    intro q hq
    exact (ENNReal.toReal_lt_of_lt_ofReal hq).le
  have hclosure : closure ((H.tubeMetric T k).ball (H.tubeBase T k) r) ⊆
      (H.tubeCriticalRegion T Acrit k : Set (T k).carrierOpen) := by
    intro q hq
    have hqr_le : ((H.tubeMetric T k).edist (H.tubeBase T k) q).toReal ≤ r :=
      hclosure_le hq
    have hqr : ((H.tubeMetric T k).edist (H.tubeBase T k) q).toReal < Acrit :=
      hqr_le.trans_lt hrA
    change (H.tubeMetric T k).edist (H.tubeBase T k) q < ENNReal.ofReal Acrit
    rw [← ENNReal.ofReal_toReal (H.tube_edist_ne_top T k _ _)]
    exact (ENNReal.ofReal_lt_ofReal_iff hA).mpr hqr
  change IsCompact (closure ((intrinsicOpenMetric (H.tubeMetric T k)
    (H.tubeCriticalRegion T Acrit k)).ball (H.tubeCriticalBase T Acrit hA k) r))
  rw [intrinsicOpenMetric_closure_ball_eq_preimage (H.tubeMetric T k)
    (H.tubeCriticalRegion T Acrit k) (H.tubeCriticalBase T Acrit hA k) hball]
  apply Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
    (H.tube_base_regular T k r hrr)
  intro q hq
  exact ⟨⟨q, hclosure hq⟩, rfl⟩



theorem tubeCritical_volume_eq (k : ℕ) :
    (H.tubeCriticalMetric T Acrit k).volumeMeasure univ =
      (H.tubeMetric T k).volumeMeasure (H.tubeCriticalRegion T Acrit k : Set _) :=
  intrinsicOpenMetric_volumeMeasure_univ (H.tubeMetric T k)
    (H.tubeCriticalRegion T Acrit k)



theorem exists_tubeCritical_volume_bound :
    ∃ V : ℝ, 0 < V ∧ ∀ k,
      (H.tubeCriticalMetric T Acrit k).volumeMeasure univ ≤ ENNReal.ofReal V := by
  obtain ⟨V, hV, hbound⟩ := H.exists_tube_volume_bound T
  refine ⟨V, hV, ?_⟩
  intro k
  rw [H.tubeCritical_volume_eq T Acrit k]
  exact (measure_mono (subset_univ _)).trans (hbound k)

end PoincareConjecture.M28.CounterexampleNeckFamily
