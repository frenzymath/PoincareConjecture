import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallFreshCore
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallStrongRadius
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.CompactStageRegularity












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

set_option maxHeartbeats 3200000 in




theorem exists_retained_fresh_core_capture
    {epsilon C A : ℝ}
    {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
      ((n : ℝ) + 1) ((n : ℝ) + 1)}
    (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
      (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))) :
    letI := G.limitCarrier.topologicalSpace
    ∀ (q : G.limitCarrier.carrier) (sigma : ℕ → ℕ), StrictMono sigma →
      ∀ (N : ∀ k, EpsilonNeck
        ((E (W.high_index (G.subsequence (sigma k)) + H.shift)).flow.metric
          (E (W.high_index (G.subsequence (sigma k)) + H.shift)).time)),
        (∀ k, (N k).epsilon = epsilon) →
        (∀ k, (N k).center = (G.embedding (sigma k) q).val.val) →
        ∀ rmin : ℝ, 0 < rmin →
          (∀ᶠ k in atTop, rmin ≤ Real.sqrt
            ((E (W.high_index (G.subsequence (sigma k)) + H.shift)).flow.scalar
              ⟨(E (W.high_index (G.subsequence (sigma k)) + H.shift)).time,
                (E (W.high_index (G.subsequence (sigma k)) + H.shift)).basepoint⟩) *
                  (N k).scale) →
          (∀ᶠ k in atTop, {x | x ∈ (N k).carrier ∧
              |((N k).coordinate_inverse x).2| ≤ 3 * epsilon⁻¹ / 4} ⊆
            (Subtype.val : (W.tube (W.high_index (G.subsequence (sigma k)))).carrierOpen →
              ((E (W.high_index (G.subsequence (sigma k)) + H.shift)).flow.slice
                (E (W.high_index (G.subsequence (sigma k)) + H.shift)).time).carrier) ''
              (H.tubeCriticalRegion W.tube W.radius (W.high_index (G.subsequence (sigma k))) :
                Set (W.tube (W.high_index (G.subsequence (sigma k)))).carrierOpen)) →
          ∃ j : ℕ, ∀ᶠ k in atTop, j ≤ sigma k ∧ ∀ x ∈ (N k).carrier,
            |((N k).coordinate_inverse x).2| ≤ 2 * epsilon⁻¹ / 3 →
              x ∈ (fun y => (G.embedding (sigma k) y).val.val) '' G.exhaustion j := by
  let := G.limitCarrier.topologicalSpace
  intro q sigma hsigma N heps hcenter rmin hrmin hfloor hslab
  obtain ⟨j, hjq⟩ : ∃ j, q ∈ G.exhaustion j := by
    have hq : q ∈ ⋃ j, G.exhaustion j := by rw [G.exhaustion_covers]; exact mem_univ _
    exact mem_iUnion.mp hq
  obtain ⟨rho, hrho, hstage⟩ := G.exists_eventual_compact_stage_regularComponent j
  have hepspos : 0 < epsilon := heps 0 ▸ (N 0).epsilon_pos
  let delta := min rho (rmin * epsilon⁻¹ / 200)
  have hdelta : 0 < delta := lt_min hrho (by positivity)
  obtain ⟨ell, hcoverage⟩ := G.regular_component_coverage delta hdelta
  refine ⟨ell, ?_⟩
  filter_upwards [hsigma.tendsto_atTop.eventually hstage,
    hsigma.tendsto_atTop.eventually hcoverage, hfloor, hslab] with k hkstage hkcover hkfloor hkslab
  let nu := W.high_index (G.subsequence (sigma k))
  have hslabN : {x | x ∈ (N k).carrier ∧
        |((N k).coordinate_inverse x).2| ≤ 3 * (N k).epsilon⁻¹ / 4} ⊆
      (Subtype.val : (W.tube nu).carrierOpen →
        ((E (nu + H.shift)).flow.slice (E (nu + H.shift)).time).carrier) ''
          (H.tubeCriticalRegion W.tube W.radius nu : Set (W.tube nu).carrierOpen) := by
    simpa only [heps k] using hkslab
  have hqreg : G.embedding (sigma k) q ∈ regularComponent
      (H.tubeCriticalMetric W.tube W.radius nu)
      (H.tubeCriticalBase W.tube W.radius W.radius_pos nu) delta :=
    regularComponent_antitone _ _ (min_le_left _ _)
      (hkstage ⟨q, subset_closure hjq, rfl⟩)
  refine ⟨hkcover.1, ?_⟩
  intro x hx hheight
  have hthree : |((N k).coordinate_inverse x).2| ≤ 3 * epsilon⁻¹ / 4 := by
    nlinarith only [hheight, inv_pos.mpr hepspos]
  obtain ⟨y, hy, hxy⟩ := hkslab ⟨hx, hthree⟩
  have hregular := H.tubeCritical_fresh_core_component W.tube W.radius W.radius_pos nu
    (N k) rmin hrmin hkfloor hslabN (G.embedding (sigma k) q) (hcenter k)
    (by simpa only [heps k] using min_le_right rho (rmin * epsilon⁻¹ / 200)) hqreg
    ⟨y, hy⟩ (by simpa only [hxy] using hx)
    (by simpa only [hxy, heps k] using hheight)
  obtain ⟨z, hz, hzy⟩ := hkcover.2 hregular
  refine ⟨z, hz, ?_⟩
  exact (congrArg (fun v : H.tubeCriticalRegion W.tube W.radius nu => v.val.val)
    hzy).trans hxy

set_option maxHeartbeats 3200000 in





theorem exists_retained_strong_neck_core_capture_accuracy
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
                ∃ j : ℕ, ∀ᶠ k in atTop, j ≤ sigma k ∧ ∀ x ∈ (J k).carrier,
                  |((J k).coordinate_inverse x).2| ≤ 2 * epsilon⁻¹ / 3 →
                    x ∈ (fun y => (G.embedding (sigma k) y).val.val) '' G.exhaustion j := by
  obtain ⟨epsilon0, hpos, hsmall, hradial⟩ :=
    exists_retained_strong_neck_radial_margin_accuracy P
  refine ⟨epsilon0, hpos, hsmall, ?_⟩
  intro epsilon C A E H W hepsilon G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D0 q L hL sigma hsigma f hf hbound hgraphs hside
  obtain ⟨J, hcenter, ha, hconv, eta, heta, _hetaR, hmargin⟩ :=
    hradial H W hepsilon G D0 q L hL sigma hsigma f hf hbound hgraphs hside
  have hhalf : epsilon < 1 / 2 := (hepsilon.trans hsmall).trans_lt (by norm_num)
  let N := fun k => strongNeck_top (J k) hhalf
  let a := (D0.scalarCurvature q)⁻¹
  let rmin := Real.sqrt (a / 2)
  have hrmin : 0 < rmin := Real.sqrt_pos.mpr (half_pos ha)
  have hfloor : ∀ᶠ k in atTop, rmin ≤ Real.sqrt
      ((E (W.high_index (G.subsequence (sigma k)) + H.shift)).flow.scalar
        ⟨(E (W.high_index (G.subsequence (sigma k)) + H.shift)).time,
          (E (W.high_index (G.subsequence (sigma k)) + H.shift)).basepoint⟩) *
            (N k).scale := by
    filter_upwards [hconv.eventually
      (eventually_ge_nhds (show a / 2 < a from half_lt_self ha))] with k hk
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg (Real.sqrt_nonneg _) (J k).scale_pos.le, ?_⟩
    rw [mul_pow, Real.sq_sqrt (H.base_scalar_pos _).le]
    exact hk
  have hslab : ∀ᶠ k in atTop, {x | x ∈ (N k).carrier ∧
        |((N k).coordinate_inverse x).2| ≤ 3 * epsilon⁻¹ / 4} ⊆
      (Subtype.val : (W.tube (W.high_index (G.subsequence (sigma k)))).carrierOpen →
        ((E (W.high_index (G.subsequence (sigma k)) + H.shift)).flow.slice
          (E (W.high_index (G.subsequence (sigma k)) + H.shift)).time).carrier) ''
        (H.tubeCriticalRegion W.tube W.radius (W.high_index (G.subsequence (sigma k))) :
          Set (W.tube (W.high_index (G.subsequence (sigma k)))).carrierOpen) := by
    filter_upwards [hmargin] with k hk
    intro x hx
    obtain ⟨hxT, hdist⟩ := hk x hx.1 hx.2
    refine ⟨⟨x, hxT⟩, ?_, rfl⟩
    change (H.tubeMetric W.tube _).edist (H.tubeBase W.tube _) ⟨x, hxT⟩ <
      ENNReal.ofReal W.radius
    have hfinite := H.tube_edist_ne_top W.tube
      (W.high_index (G.subsequence (sigma k))) (H.tubeBase W.tube _) ⟨x, hxT⟩
    rw [← ENNReal.ofReal_toReal hfinite]
    exact (ENNReal.ofReal_lt_ofReal_iff W.radius_pos).mpr (by linarith)
  obtain ⟨j, hcapture⟩ := H.exists_retained_fresh_core_capture W G q sigma hsigma N
    (fun _ => rfl) hcenter rmin hrmin hfloor hslab
  exact ⟨J, hcenter, ha, hconv, j, hcapture⟩

end PoincareConjecture.M28.CounterexampleNeckFamily
