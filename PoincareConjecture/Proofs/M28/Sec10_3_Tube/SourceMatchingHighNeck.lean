import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallCompactScalar
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CriticalBallSourcePacket
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderUniformScalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

theorem exists_matching_high_neck_scalar_accuracy :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 200 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H) (B : ℝ),
        ∀ᶠ k in atTop, ∀ N : EpsilonNeck
          ((E (W.high_index k + H.shift)).flow.metric
            (E (W.high_index k + H.shift)).time),
          N.epsilon ≤ epsilon0 → (W.high_point k).val ∈ N.carrier →
          ∀ x ∈ N.carrier,
            B < (H.normalizedSliceConnection (W.high_index k)).scalarCurvature x := by
  obtain ⟨epsilon0, hpos, hsmall, hratio⟩ := tube.exists_cylinder_scalar_ratio_accuracy.{u}
  refine ⟨epsilon0, hpos, hsmall, ?_⟩
  intro epsilon C A E H W B
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (2 * B))]
    with k hk
  intro N heps hp x hx
  have hraw := hratio _ _
    ((E (W.high_index k + H.shift)).flow.connection
      (E (W.high_index k + H.shift)).time) N heps (W.high_point k).val hp x hx
  have hnormalized :
      (H.normalizedSliceConnection (W.high_index k)).scalarCurvature
        (W.high_point k).val ≤
      2 * (H.normalizedSliceConnection (W.high_index k)).scalarCurvature x := by
    rw [H.normalizedSlice_scalar_eq, H.normalizedSlice_scalar_eq, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hraw (H.base_scalar_pos (W.high_index k)).le
  have hhigh := W.high_scalar_lower k
  rw [H.tube_scalar_eq] at hhigh
  linarith only [hk, hhigh, hnormalized]

set_option maxHeartbeats 1600000 in

theorem exists_matching_high_neck_compact_exclusion_accuracy :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 200 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H)
        (G : RegularPointedMetricConvergence
          (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
          (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))),
        letI := G.limitCarrier.topologicalSpace
        letI := G.limitCarrier.chartedSpace
        letI := G.limitCarrier.isManifold
        ∀ (_D0 : LeviCivitaData G.limitMetric) (K : Set G.limitCarrier.carrier),
          IsCompact K → ∀ (sigma : ℕ → ℕ), StrictMono sigma →
          ∀ᶠ k in atTop, ∀ N : EpsilonNeck
            ((E (W.high_index (G.subsequence (sigma k)) + H.shift)).flow.metric
              (E (W.high_index (G.subsequence (sigma k)) + H.shift)).time),
            N.epsilon ≤ epsilon0 →
            (W.high_point (G.subsequence (sigma k))).val ∈ N.carrier →
            Disjoint N.carrier ((fun x => (G.embedding (sigma k) x).val.val) '' K) := by
  obtain ⟨epsilon0, hpos, hsmall, hhigh⟩ := exists_matching_high_neck_scalar_accuracy.{u}
  refine ⟨epsilon0, hpos, hsmall, ?_⟩
  intro epsilon C A E H W G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D0 K hK sigma hsigma
  obtain ⟨B, _, hB⟩ := H.exists_eventual_compact_normalized_raw_scalar_bound
    W.tube W.radius W.radius_pos W.high_index G D0 K hK
  have hindices := G.subsequence_strictMono.comp hsigma
  filter_upwards [hsigma.tendsto_atTop.eventually hB,
    hindices.tendsto_atTop.eventually (hhigh H W B)] with k hk hhighK
  intro N heps hp
  apply disjoint_left.mpr
  rintro x hx ⟨y, hy, rfl⟩
  exact (not_lt_of_ge ((le_abs_self _).trans (hk y hy))) (hhighK N heps hp _ hx)

end PoincareConjecture.M28.CounterexampleNeckFamily
