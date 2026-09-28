import PoincareConjecture.Proofs.M32.Claim11_34.InverseConfinement
import PoincareConjecture.Proofs.M32.Claim11_34.ZeroSlicePoint
import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.Uniqueness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

theorem blowup_exists_compact_capture_for_old_cylinders
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) {A T a : ℝ}
    (hA : 0 < A) (haJ : a ∈ J) (ha : a ∈ Icc (-T) 0) :
    ∃ K : Set G.limit.carrier.carrier, IsCompact K ∧
      ∀ᶠ k in atTop, ∃ hak : a ∈ Icc (-G.exhaustion.time k) 0,
        K ⊆ G.exhaustion.space k ∧ ∀ B eta : ℝ,
        ∀ old : ControlledBlowupCylinder S (G.subsequence k) (A + 1) T B eta,
        ∀ y ∈ closure (S.baseBall (G.subsequence k) A), ∃ z ∈ K,
          old.embedding.pointMap a ha y = (G.embedding k).pointMap a hak z := by
  let g := G.limit.flow.metric 0
  let K : Set G.limit.carrier.carrier :=
    {z | g.edist G.limit.base z ≤ ENNReal.ofReal (2 * (A + 1) + 1)}
  have hK : IsCompact K := g.isCompact_closedBall_of_metricComplete
    (G.limit.complete 0 G.limit.zero_mem) G.limit.base (2 * (A + 1) + 1)
  obtain ⟨j, hj⟩ := blowup_exists_exhaustion_superset G hK
  have htime : ∀ᶠ k in atTop, a ∈ Icc (-G.exhaustion.time k) 0 :=
    (G.exhaustion.time_cofinal {a} isCompact_singleton
      (singleton_subset_iff.mpr haJ)).mono fun _ hk => hk (mem_singleton a)
  refine ⟨K, hK, ?_⟩
  filter_upwards [blowup_eventually_zeroSliceEmbedding_inverse_ball G
    (show 0 < A + 1 by linarith) (by norm_num : (1 : ℝ) < 2),
    eventually_ge_atTop j, htime] with k hinverse hjk hak
  have hKsource : K ⊆ G.exhaustion.space k :=
    hj.trans (G.exhaustion.space_increasing hjk)
  refine ⟨hak, hKsource, ?_⟩
  intro B eta old y hy
  let gsource := (S.flow (G.subsequence k)).metric (S.base (G.subsequence k)).1
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : ((S.flow (G.subsequence k)).slice
        (S.base (G.subsequence k)).1).carrier → Type _) := ⟨gsource.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : ((S.flow (G.subsequence k)).slice
        (S.base (G.subsequence k)).1).carrier → Type _) :=
    ⟨⟨gsource.inner, gsource.toContinuousRiemannianMetric.continuous,
      fun _ _ _ => rfl⟩⟩
  let : EMetricSpace ((S.flow (G.subsequence k)).slice
      (S.base (G.subsequence k)).1).carrier := EMetricSpace.ofRiemannianMetric (𝓡 3) _
  have hsqrt : 0 < Real.sqrt (S.scale (G.subsequence k)) :=
    Real.sqrt_pos.mpr (S.base_scalar_pos (G.subsequence k))
  have hclosure : closure (S.baseBall (G.subsequence k) A) ⊆
      {x | gsource.edist (S.base (G.subsequence k)).2 x ≤
        ENNReal.ofReal (A / Real.sqrt (S.scale (G.subsequence k)))} := by
    apply closure_minimal
    · intro x hx
      exact (show gsource.edist (S.base (G.subsequence k)).2 x <
        ENNReal.ofReal (A / Real.sqrt (S.scale (G.subsequence k))) from hx).le
    · exact isClosed_le (continuous_const.edist continuous_id) continuous_const
  have hyW : y ∈ S.baseBall (G.subsequence k) (A + 1) :=
    (hclosure hy).trans_lt ((ENNReal.ofReal_lt_ofReal_iff
      (div_pos (show 0 < A + 1 by linarith) hsqrt)).mpr
      ((div_lt_div_iff_of_pos_right hsqrt).mpr (by linarith)))
  obtain ⟨hytarget, hzinball⟩ := hinverse y hyW
  let z := (blowup_zeroSliceEmbedding G k).symm y
  have hzK : z ∈ K :=
    (show g.edist G.limit.base z < ENNReal.ofReal (2 * (A + 1)) from hzinball).le.trans
      (ENNReal.ofReal_le_ofReal (by linarith))
  have hzeroOld : (0 : ℝ) ∈ Icc (-T) 0 := ⟨ha.1.trans ha.2, le_rfl⟩
  have hzeroG : (0 : ℝ) ∈ Icc (-G.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
  have hzero : old.embedding.pointMap 0 hzeroOld y =
      (G.embedding k).pointMap 0 hzeroG z := by
    rw [old.zero_identity hzeroOld y hyW, blowup_zeroSliceEmbedding_pointMap]
    rw [(blowup_zeroSliceEmbedding G k).right_inv hytarget]
  exact ⟨z, hzK, cylinder_pointMap_eq_on_overlap old.embedding (G.embedding k)
    ordConnected_Icc ordConnected_Icc hyW (hKsource hzK) hzeroOld hzeroG hzero a ha hak⟩

end PoincareConjecture.M32
