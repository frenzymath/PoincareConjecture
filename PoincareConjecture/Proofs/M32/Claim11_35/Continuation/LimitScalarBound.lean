import PoincareConjecture.Proofs.M32.Claim11_34.ZeroSlicePoint
import PoincareConjecture.Proofs.M32.Claim11_34.ForwardComparison
import PoincareConjecture.Proofs.M32.Claim11_34.SliceCurvatureComparison
import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.Uniqueness
import Mathlib.Algebra.Order.Archimedean.Basic












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space




theorem blowup_scalar_le_of_step_cylinders
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) {M B c : ℝ} (hc : 0 < c)
    (hstage : ∀ n : ℕ, ∀ A : ℝ, 0 < A → ∀ᶠ k in atTop,
      ∃ e : ControlledBlowupCylinder S k A ((n : ℝ) * c) B 1,
        ∀ s hs x, x ∈ S.baseBall k A →
          (S.flow k).scalar (e.embedding.pointMap s hs x) ≤ M * S.scale k) :
    ∀ t ∈ J, ∀ x : G.limit.carrier.carrier,
      (G.limit.flow.connection t).scalarCurvature x ≤ M := by
  intro t ht x
  have htime := G.exhaustion.time_cofinal {t} isCompact_singleton
    (singleton_subset_iff.mpr ht)
  obtain ⟨j, hj⟩ := htime.exists
  have htzero : t ≤ 0 := (hj (mem_singleton t)).2
  obtain ⟨n, hn⟩ := exists_nat_gt ((|t| + 1) / c)
  have hnlarge : |t| + 1 < (n : ℝ) * c := (div_lt_iff₀ hc).mp hn
  have htold : t ∈ Icc (-((n : ℝ) * c)) 0 := by
    exact ⟨by linarith [neg_abs_le t], htzero⟩
  have hzeroOld : (0 : ℝ) ∈ Icc (-((n : ℝ) * c)) 0 :=
    ⟨by nlinarith [Nat.cast_nonneg (α := ℝ) n], le_rfl⟩
  let g := G.limit.flow.metric 0
  let : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace
  let : MetricSpace G.limit.carrier.carrier := g.toMetricSpace
  let r := dist x G.limit.base + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hx : x ∈ g.ball G.limit.base r := by
    rw [← g.toMetricSpace_ball]
    change dist x G.limit.base < r
    dsimp [r]
    linarith
  have himages := blowup_eventually_zeroSliceEmbedding_image_ball G hr
    (by norm_num : (1 : ℝ) < 2)
  have hstages := G.subsequence_strictMono.tendsto_atTop.eventually
    (hstage n (2 * r) (by positivity))
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  have hevent : ∀ᶠ _k : ℕ in atTop,
      (G.limit.flow.connection t).scalarCurvature x ≤ M + epsilon := by
    filter_upwards [himages, hstages,
      blowup_eventually_sliceScalar_error G ht (isCompact_singleton (x := x)) hepsilon]
      with k himages hstages hcompare
    obtain ⟨e, hbound⟩ := hstages
    obtain ⟨htk, _, herror⟩ := hcompare
    let y := blowup_zeroSliceEmbedding G k x
    have hy : y ∈ S.baseBall (G.subsequence k) (2 * r) :=
      himages.2 (mem_image_of_mem _ hx)
    have hxsource : x ∈ G.exhaustion.space k := by
      simpa only [blowup_zeroSliceEmbedding_source] using himages.1 hx
    have hzero : (0 : ℝ) ∈ Icc (-G.exhaustion.time k) 0 :=
      ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
    have hanchor : e.embedding.pointMap 0 hzeroOld y =
        (G.embedding k).pointMap 0 hzero x := by
      rw [e.zero_identity hzeroOld y hy, blowup_zeroSliceEmbedding_pointMap]
    have hsame := cylinder_pointMap_eq_on_overlap e.embedding (G.embedding k)
      ordConnected_Icc ordConnected_Icc hy hxsource hzeroOld hzero hanchor t htold htk
    have hsource := hbound t htold y hy
    rw [hsame] at hsource
    have hnormalized :
        (S.flow (G.subsequence k)).scalar ((G.embedding k).pointMap t htk x) /
          S.scale (G.subsequence k) ≤ M :=
      (div_le_iff₀ (S.base_scalar_pos (G.subsequence k))).mpr hsource
    have herr := herror x (mem_singleton x)
    linarith [(abs_lt.mp herr).1]
  exact hevent.exists.choose_spec

end PoincareConjecture.M32
