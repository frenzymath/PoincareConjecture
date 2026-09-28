import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallFreshNeck
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SeparatingLimitCover












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

set_option maxHeartbeats 3200000 in





theorem exists_retained_positive_side_tube_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 10000 : ℝ) ∧
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
          ∀ (D0 : LeviCivitaData G.limitMetric) (L : EpsilonNeck G.limitMetric),
            L.center = G.base → L.epsilon = 3 * epsilon / 2 → L.IsSeparating →
            ∀ X : Set G.limitCarrier.carrier, IsConnected X → frontier X = L.central_sphere →
            ∀ (sigma : ℕ → ℕ), StrictMono sigma →
            ∀ (f : ℕ → UnitTwoSphere → ℝ),
              (∀ k, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (f k)) →
              (∀ k z, |f k z| < epsilon⁻¹ / 32) →
              (∀ k, (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
                W.high_index G (sigma k)) '' L.central_sphere =
                  range (fun z =>
                    ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.coordinate_map
                      (z, f k z))) →
              (∀ x ∈ X, ∀ᶠ k in atTop, (G.embedding (sigma k) x).val.val ∉
                ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28
                  (f k)) →
              ∃ K : NeckOnlyCover G.limitMetric, K.X = X ∧ K.epsilon = 2 * epsilon ∧
                (∀ N ∈ K.necks, N.center ∈ X ∧ N.connection = D0) ∧
                  Nonempty (CorrectedA19Conclusion G.limitMetric K) := by
  classical
  obtain ⟨epsilonN, hNpos, hNsmall, hneck⟩ := exists_retained_positive_limit_neck_accuracy P
  obtain ⟨epsilonT, hTpos, hTsmall, htube⟩ := exists_limit_cover_tube_accuracy.{0}
  refine ⟨min epsilonN (epsilonT / 2), lt_min hNpos (half_pos hTpos),
    (min_le_left _ _).trans hNsmall, ?_⟩
  intro epsilon C A E H W hepsilon G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  let := G.limitCarrier.measurableSpace
  let := G.limitCarrier.borelSpace
  let := G.limitCarrier.t2Space
  let := G.limitCarrier.t3Space
  intro D0 L hL hepsL hsep X hX hfront sigma hsigma f hf hbound hgraphs hside
  have hepspos : 0 < epsilon :=
    (H.segment 0).cover_epsilon ▸ (H.segment 0).cover.epsilon_pos
  have hepsN : epsilon ≤ epsilonN := hepsilon.trans (min_le_left _ _)
  have htwo : 2 * epsilon ≤ epsilonT := by
    have hh := hepsilon.trans (min_le_right _ _)
    linarith
  have hhalf : 2 * epsilon < 1 / 2 := (htwo.trans hTsmall).trans_lt (by norm_num)
  have hpoint (x : X) : ∃ N : EpsilonNeck G.limitMetric,
      N.epsilon = 2 * epsilon ∧ N.center = x.val ∧ N.connection = D0 := by
    obtain ⟨N, heps, hcenter, hconnection, _hstage⟩ :=
      hneck H W hepsN G D0 x.val L hL sigma hsigma f hf hbound hgraphs (hside x.val x.property)
    have hNeps : N.epsilon ≤ 2 * epsilon := by rw [heps]; linarith
    exact ⟨N.restrict_m28 (2 * epsilon) hNeps hhalf, rfl, hcenter, hconnection⟩
  choose N hN using hpoint
  let K : NeckOnlyCover G.limitMetric := {
    epsilon := 2 * epsilon
    epsilon_pos := mul_pos (by norm_num) hepspos
    epsilon_threshold := epsilonT
    epsilon_threshold_pos := hTpos
    epsilon_threshold_le_one_two_hundred := hTsmall
    epsilon_le_threshold := htwo
    X := X
    connected_X := hX
    necks := range N
    pointwise_center_cover := fun x hx =>
      ⟨N ⟨x, hx⟩, mem_range_self _, (hN ⟨x, hx⟩).2.1⟩
    neck_epsilon := by
      rintro _ ⟨x, rfl⟩
      exact (hN x).1 }
  have hcenters : ∀ V ∈ K.necks, V.center ∈ X ∧ V.connection = D0 := by
    rintro _ ⟨x, rfl⟩
    refine ⟨?_, (hN x).2.2⟩
    rw [(hN x).2.1]
    exact x.property
  have hclosure : L.center ∈ closure K.X := by
    apply frontier_subset_closure
    change L.center ∈ frontier X
    rw [hfront]
    exact L.center_on_central_sphere
  have hLsmall : L.epsilon ≤ epsilonT := by rw [hepsL]; linarith
  obtain ⟨_hseparate, hresult⟩ := htube K L htwo hLsmall hsep hclosure
    (fun V hV => (hcenters V hV).1)
  exact ⟨K, rfl, rfl, hcenters, hresult⟩

end PoincareConjecture.M28.CounterexampleNeckFamily
