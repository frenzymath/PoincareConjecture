import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallFreshRadius
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallNeckScales
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallRawStage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

set_option maxHeartbeats 3200000 in

theorem exists_retained_strong_neck_radial_margin_accuracy
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
                0 < (D0.scalarCurvature q)⁻¹ ∧
                Tendsto (fun k =>
                  (E (W.high_index (G.subsequence (sigma k)) + H.shift)).flow.scalar
                    ⟨(E (W.high_index (G.subsequence (sigma k)) + H.shift)).time,
                      (E (W.high_index (G.subsequence (sigma k)) + H.shift)).basepoint⟩ *
                        (J k).scale ^ 2) atTop (𝓝 (D0.scalarCurvature q)⁻¹) ∧
                ∃ eta : ℝ, 0 < eta ∧ eta < W.radius ∧ ∀ᶠ k in atTop,
                  ∀ x ∈ (J k).carrier,
                    |((J k).coordinate_inverse x).2| ≤ 3 * epsilon⁻¹ / 4 →
                    ∃ hx : x ∈ (W.tube
                      (W.high_index (G.subsequence (sigma k)))).carrierOpen,
                      ((H.tubeMetric W.tube (W.high_index (G.subsequence (sigma k)))).edist
                        (H.tubeBase W.tube (W.high_index (G.subsequence (sigma k))))
                        ⟨x, hx⟩).toReal < W.radius - eta := by
  obtain ⟨epsilonR, hRpos, hRsmall, hradial⟩ :=
    exists_retained_fresh_slab_radial_margin_accuracy.{u}
  obtain ⟨epsilonS, hSpos, _, hscales⟩ :=
    exists_source_criticalBall_neck_scale_limits_accuracy P
  refine ⟨min epsilonR epsilonS, lt_min hRpos hSpos,
    (min_le_left _ _).trans hRsmall, ?_⟩
  intro epsilon C A E H W hepsilon G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D0 q L hL sigma hsigma f hf hbound hgraphs hside
  have hepsR : epsilon ≤ epsilonR := hepsilon.trans (min_le_left _ _)
  have hepsS : epsilon ≤ epsilonS := hepsilon.trans (min_le_right _ _)
  have hhalf : epsilon < 1 / 2 := (hepsR.trans hRsmall).trans_lt (by norm_num)
  obtain ⟨J0, hcenter, ha, hconv, hscale⟩ :=
    hscales H W.tube hepsS W.radius W.radius_pos W.high_index G D0 q
  let J := fun k => J0 (sigma k)
  let N := fun k => strongNeck_top (J k) hhalf
  let a := (D0.scalarCurvature q)⁻¹
  let rmin := Real.sqrt (a / 2)
  have hrmin : 0 < rmin := Real.sqrt_pos.mpr (half_pos ha)
  have hfloor : ∀ᶠ k in atTop, rmin ≤ Real.sqrt
      ((E (W.high_index (G.subsequence (sigma k)) + H.shift)).flow.scalar
        ⟨(E (W.high_index (G.subsequence (sigma k)) + H.shift)).time,
          (E (W.high_index (G.subsequence (sigma k)) + H.shift)).basepoint⟩) *
            (N k).scale := by
    filter_upwards [hsigma.tendsto_atTop.eventually hscale] with k hk
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg (Real.sqrt_nonneg _) (J k).scale_pos.le, ?_⟩
    rw [mul_pow, Real.sq_sqrt (H.base_scalar_pos _).le]
    exact hk.1
  have hbase (k : ℕ) :
      (H.tubeBase W.tube (W.high_index (G.subsequence (sigma k)))).val ∈
        range (fun z =>
          ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.coordinate_map
            (z, f k z)) := by
    have hb : G.base ∈ L.central_sphere := hL ▸ L.center_on_central_sphere
    have hh := mem_image_of_mem
      (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
        W.high_index G (sigma k)) hb
    rw [hgraphs k] at hh
    simpa only [H.regularRawStageDiffeomorph_base, tubeBase] using hh
  have hlabels : ∀ᶠ k in atTop,
      (H.tubeBase W.tube (W.high_index (G.subsequence (sigma k)))).val ∈
        range (fun z =>
          ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.coordinate_map
            (z, f k z)) ∧
      (N k).center ∉
        ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28 (f k) := by
    filter_upwards [hside] with k hk
    refine ⟨hbase k, ?_⟩
    change (J0 (sigma k)).center ∉ _
    rwa [hcenter]
  obtain ⟨eta, heta, hetaR, hmargin⟩ := hradial H W hepsR G D0 q sigma hsigma N
    (fun _ => rfl) (fun k => hcenter (sigma k)) f hf hbound hlabels rmin hrmin hfloor
  exact ⟨J, (fun k => hcenter (sigma k)), ha, hconv.comp hsigma.tendsto_atTop,
    eta, heta, hetaR, hmargin⟩

end PoincareConjecture.M28.CounterexampleNeckFamily
