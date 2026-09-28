import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceMatchingHighNeck
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallInitialNodeCapture











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

set_option maxHeartbeats 1600000 in





theorem exists_matching_high_neck_separation_accuracy :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 200 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H),
        epsilon ≤ epsilon0 →
        ∀ (G : RegularPointedMetricConvergence
          (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
          (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))),
          letI := G.limitCarrier.topologicalSpace
          letI := G.limitCarrier.chartedSpace
          letI := G.limitCarrier.isManifold
          ∀ (_D0 : LeviCivitaData G.limitMetric) (q : G.limitCarrier.carrier)
            (sigma : ℕ → ℕ), StrictMono sigma →
            ∀ (J : ∀ k, EpsilonNeck
              ((E (W.high_index (G.subsequence (sigma k)) + H.shift)).flow.metric
                (E (W.high_index (G.subsequence (sigma k)) + H.shift)).time)),
              (∀ k, (J k).epsilon = epsilon) →
              (∀ k, (J k).center = (G.embedding (sigma k) q).val.val) →
              ∀ᶠ k in atTop, ∀ P : EpsilonNeck
                ((E (W.high_index (G.subsequence (sigma k)) + H.shift)).flow.metric
                  (E (W.high_index (G.subsequence (sigma k)) + H.shift)).time),
                P.epsilon ≤ epsilon0 →
                (W.high_point (G.subsequence (sigma k))).val ∈ P.carrier →
                Disjoint P.carrier
                  ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.carrier ∧
                Disjoint P.carrier (J k).carrier := by
  obtain ⟨epsilonH, hHpos, hHsmall, hhigh⟩ := exists_matching_high_neck_scalar_accuracy.{u}
  obtain ⟨epsilonR, hRpos, _, hratio⟩ := tube.exists_cylinder_scalar_ratio_accuracy.{u}
  refine ⟨min epsilonH epsilonR, lt_min hHpos hRpos,
    (min_le_left _ _).trans hHsmall, ?_⟩
  intro epsilon C A E H W hepsilon G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D0 q sigma hsigma J heps hcenter
  let nu := fun k => W.high_index (G.subsequence (sigma k))
  obtain ⟨B, _, hB⟩ := H.exists_eventual_compact_normalized_raw_scalar_bound
    W.tube W.radius W.radius_pos W.high_index G D0 {q} isCompact_singleton
  have hindices := G.subsequence_strictMono.comp hsigma
  have hhighTail := hindices.tendsto_atTop.eventually
    (hhigh H W (max (2 * B) (32 * (max C 2) ^ 2)))
  filter_upwards [hsigma.tendsto_atTop.eventually hB, hhighTail] with k hk hhighK
  have hcenterB : (H.normalizedSliceConnection (nu k)).scalarCurvature (J k).center ≤ B := by
    rw [hcenter]
    exact (le_abs_self _).trans (hk q (mem_singleton q))
  have hJbound : ∀ x ∈ (J k).carrier,
      (H.normalizedSliceConnection (nu k)).scalarCurvature x ≤ 2 * B := by
    intro x hx
    have hraw := hratio _ _
      ((E (nu k + H.shift)).flow.connection (E (nu k + H.shift)).time) (J k)
      ((heps k).trans_le (hepsilon.trans (min_le_right _ _))) x hx (J k).center
      ((J k).central_sphere_subset (J k).center_on_central_sphere)
    have hh : (H.normalizedSliceConnection (nu k)).scalarCurvature x ≤
        2 * (H.normalizedSliceConnection (nu k)).scalarCurvature (J k).center := by
      rw [H.normalizedSlice_scalar_eq, H.normalizedSlice_scalar_eq, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right hraw (H.base_scalar_pos (nu k)).le
    linarith only [hh, hcenterB]
  have hN0bound : ∀ x ∈ ((W.tube (nu k)).list.node 0).2.carrier,
      (H.normalizedSliceConnection (nu k)).scalarCurvature x ≤ 32 * (max C 2) ^ 2 := by
    intro x hx
    let N0 := ((W.tube (nu k)).list.node 0).2
    have hraw := hratio _ _
      ((E (nu k + H.shift)).flow.connection (E (nu k + H.shift)).time) N0
      ((W.tube (nu k)).initial_node_geometry.1.trans_le
        (hepsilon.trans (min_le_right _ _))) x hx N0.center
      (N0.central_sphere_subset N0.center_on_central_sphere)
    change (E (nu k + H.shift)).flow.scalar ⟨(E (nu k + H.shift)).time, x⟩ ≤
      2 * (E (nu k + H.shift)).flow.scalar ⟨(E (nu k + H.shift)).time, N0.center⟩ at hraw
    rw [(W.tube (nu k)).node_zero_readout.2.2, (H.segment (nu k)).lower_scalar] at hraw
    rw [H.normalizedSlice_scalar_eq]
    apply (div_le_iff₀ (H.base_scalar_pos (nu k))).mpr
    nlinarith only [hraw]
  intro P hepsP hp
  have hP := hhighK P (hepsP.trans (min_le_left _ _)) hp
  constructor
  · apply Set.disjoint_left.mpr
    intro x hxP hx0
    exact (not_lt_of_ge ((hN0bound x hx0).trans (le_max_right _ _))) (hP x hxP)
  · apply Set.disjoint_left.mpr
    intro x hxP hxJ
    exact (not_lt_of_ge ((hJbound x hxJ).trans (le_max_left _ _))) (hP x hxP)

end PoincareConjecture.M28.CounterexampleNeckFamily
