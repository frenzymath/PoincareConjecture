import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallWholeNeighborhood
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallFreshNeck











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

set_option maxHeartbeats 3200000 in




theorem exists_retained_whole_neighborhood_capture_accuracy
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
          ∀ (D0 : LeviCivitaData G.limitMetric) (q : G.limitCarrier.carrier)
            (L : EpsilonNeck G.limitMetric), L.center = G.base →
            ∀ (sigma : ℕ → ℕ), StrictMono sigma →
            ∀ (f : ℕ → UnitTwoSphere → ℝ),
              (∀ k, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (f k)) →
              (∀ k z, |f k z| < epsilon⁻¹ / 32) →
              (∀ k, (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
                W.high_index G (sigma k)) '' L.central_sphere =
                  range (fun z =>
                    ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.coordinate_map
                      (z, f k z))) →
              (∀ᶠ k in atTop, (G.embedding (sigma k) q).val.val ∉
                ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28
                  (f k)) →
              ∃ J : ∀ k, GeneralizedStrongNeck
                (E (W.high_index (G.subsequence (sigma k)) + H.shift)).flow
                (E (W.high_index (G.subsequence (sigma k)) + H.shift)).time epsilon,
                (∀ k, (J k).center = (G.embedding (sigma k) q).val.val) ∧
                ∃ V : EpsilonNeck G.limitMetric,
                  V.epsilon = 3 * epsilon / 2 ∧ V.center = q ∧ V.connection = D0 ∧
                  (∃ j : ℕ, V.carrier ⊆ G.exhaustion j) ∧
                  Tendsto (fun k =>
                    (E (W.high_index (G.subsequence (sigma k)) + H.shift)).flow.scalar
                      ⟨(E (W.high_index (G.subsequence (sigma k)) + H.shift)).time,
                        (E (W.high_index (G.subsequence (sigma k)) + H.shift)).basepoint⟩ *
                          (J k).scale ^ 2) atTop (𝓝 (V.scale ^ 2)) ∧
                  ∀ᶠ k in atTop, ∀ y ∈ V.carrier,
                    |(V.coordinate_inverse y).2| ≤ 3 * epsilon⁻¹ / 5 →
                      (G.embedding (sigma k) y).val.val ∈ (J k).carrier ∧
                      |((J k).coordinate_inverse (G.embedding (sigma k) y).val.val).2| <
                        3 * epsilon⁻¹ / 4 := by
  obtain ⟨epsilon0, hpos, hsmall, hcore⟩ :=
    exists_retained_strong_neck_core_capture_accuracy P
  refine ⟨epsilon0, hpos, hsmall, ?_⟩
  intro epsilon C A E H W hepsilon G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D0 q L hL sigma hsigma f hf hbound hgraphs hside
  obtain ⟨J, hcenter, ha, hconv, j, hcapture⟩ :=
    hcore H W hepsilon G D0 q L hL sigma hsigma f hf hbound hgraphs hside
  have hthird : epsilon < 1 / 3 := (hepsilon.trans hsmall).trans_lt (by norm_num)
  have hhalf : epsilon < 1 / 2 := hthird.trans (by norm_num)
  let N := fun k => strongNeck_top (J k) hhalf
  obtain ⟨k, hk⟩ := (H.exists_retained_fresh_neck W G D0 q (inv_pos.mp ha) hthird
    sigma hsigma N (fun _ => rfl) hcenter hconv j hcapture).exists
  obtain ⟨_, V, hepsV, hcenterV, hscaleV, hconnectionV, hcarrierV, _⟩ := hk
  have hscaleSq : V.scale ^ 2 = (D0.scalarCurvature q)⁻¹ := by
    rw [hscaleV, ← Real.rpow_mul_natCast (inv_pos.mp ha).le (-1 / 2) 2]
    norm_num [Real.rpow_neg_one]
  have hconvV : Tendsto (fun k =>
      (E (W.high_index (G.subsequence (sigma k)) + H.shift)).flow.scalar
        ⟨(E (W.high_index (G.subsequence (sigma k)) + H.shift)).time,
          (E (W.high_index (G.subsequence (sigma k)) + H.shift)).basepoint⟩ *
            (J k).scale ^ 2) atTop (𝓝 (V.scale ^ 2)) := by
    rwa [hscaleSq]
  have hfloor : ∀ᶠ k in atTop, (9 / 10 : ℝ) * V.scale ≤ Real.sqrt
      ((E (W.high_index (G.subsequence (sigma k)) + H.shift)).flow.scalar
        ⟨(E (W.high_index (G.subsequence (sigma k)) + H.shift)).time,
          (E (W.high_index (G.subsequence (sigma k)) + H.shift)).basepoint⟩) *
            (N k).scale := by
    have hlt : (81 / 100 : ℝ) * V.scale ^ 2 < V.scale ^ 2 := by
      nlinarith only [sq_pos_of_pos V.scale_pos]
    filter_upwards [hconvV.eventually (eventually_ge_nhds hlt)] with k hk
    apply (sq_le_sq₀ (mul_nonneg (by norm_num) V.scale_pos.le)
      (mul_nonneg (Real.sqrt_nonneg _) (N k).scale_pos.le)).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt (H.base_scalar_pos _).le]
    simpa only [N, strongNeck_top, show (9 / 10 : ℝ) ^ 2 = 81 / 100 by norm_num]
      using hk
  refine ⟨J, hcenter, V, hepsV, hcenterV, hconnectionV, ⟨j, hcarrierV⟩, hconvV, ?_⟩
  exact H.eventually_retained_whole_neighborhood_in_core W (hepsilon.trans hsmall) G
    V hepsV sigma hsigma N (fun _ => rfl)
    (fun k => by
      change (J k).center = _
      rw [hcenterV]
      exact hcenter k) hfloor

end PoincareConjecture.M28.CounterexampleNeckFamily
