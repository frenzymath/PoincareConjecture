import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeFreshSlab
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeSharpScalar
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeTerminalScalar
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallCompactScalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

set_option maxHeartbeats 2400000 in

theorem exists_retained_fresh_slab_accuracy :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 200 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E) (T : ∀ k, SourceTubeData (H.segment k)),
        epsilon ≤ epsilon0 → ∀ (A1 : ℝ) (hA1 : 0 < A1) (phi : ℕ → ℕ),
          StrictMono phi →
          ∀ (G : RegularPointedMetricConvergence
            (fun k => H.tubeCriticalMetric T A1 (phi k))
            (fun k => H.tubeCriticalBase T A1 hA1 (phi k))),
          letI := G.limitCarrier.topologicalSpace
          letI := G.limitCarrier.chartedSpace
          letI := G.limitCarrier.isManifold
          ∀ (_D0 : LeviCivitaData G.limitMetric) (q : G.limitCarrier.carrier)
            (sigma : ℕ → ℕ), StrictMono sigma →
            ∀ (J : ∀ k, EpsilonNeck
              ((E (phi (G.subsequence (sigma k)) + H.shift)).flow.metric
                (E (phi (G.subsequence (sigma k)) + H.shift)).time)),
              (∀ k, (J k).epsilon = epsilon) →
              (∀ k, (J k).center = (G.embedding (sigma k) q).val.val) →
              ∀ (f : ℕ → UnitTwoSphere → ℝ), (∀ k, Continuous (f k)) →
                (∀ k z, |f k z| < epsilon⁻¹ / 32) →
                (∀ᶠ k in atTop, (G.embedding (sigma k) q).val.val ∉
                  ((T (phi (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28 (f k)) →
                ∀ᶠ k in atTop,
                  (J k).coordinate_map ''
                    (univ ×ˢ Icc (-(3 * epsilon⁻¹ / 4)) (3 * epsilon⁻¹ / 4)) ⊆
                      (T (phi (G.subsequence (sigma k)))).carrierOpen := by
  obtain ⟨epsilonS, hSpos, _, hscale⟩ := exists_source_tube_fresh_scale_accuracy.{u}
  obtain ⟨epsilonT, hTpos, _, hexclude⟩ := exists_source_terminal_neck_exclusion_accuracy.{u}
  refine ⟨min (1 / 10000) (min epsilonS epsilonT),
    lt_min (by norm_num) (lt_min hSpos hTpos),
    (min_le_left _ _).trans (by norm_num), ?_⟩
  intro epsilon C A E H T hepsilon A1 hA1 phi hphi G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D0 q sigma hsigma J heps hcenter f hf hbound hside
  let nu := fun k => phi (G.subsequence (sigma k))
  have hnu : StrictMono nu := hphi.comp (G.subsequence_strictMono.comp hsigma)
  have hcenterT (k : ℕ) : (J k).center ∈ (T (nu k)).carrierOpen := by
    rw [hcenter]
    exact (G.embedding (sigma k) q).val.property
  obtain ⟨B, _, hB⟩ := H.exists_eventual_compact_normalized_raw_scalar_bound T A1 hA1
    phi G D0 {q} isCompact_singleton
  have hcenterB : ∀ᶠ k in atTop,
      (H.normalizedSliceConnection (nu k)).scalarCurvature (J k).center ≤ B := by
    filter_upwards [hsigma.tendsto_atTop.eventually hB] with k hk
    rw [hcenter]
    exact (le_abs_self _).trans (hk q (mem_singleton q))
  have hterminal := hexclude H T
    (hepsilon.trans ((min_le_right _ _).trans (min_le_right _ _)))
    nu hnu J heps B hcenterB
  filter_upwards [hterminal, hside] with k hk hsidek
  apply (T (nu k)).fresh_three_quarter_slab_subset
    (hepsilon.trans (min_le_left _ _)) (f k) (hf k) (hbound k)
    (J k) (heps k) _ (hcenterT k) (by rwa [hcenter]) hk
  have hs := hscale H T
    (hepsilon.trans ((min_le_right _ _).trans (min_le_left _ _)))
    (nu k) (J k) (hcenterT k)
  have hzero := H.normalizedSlice_low_neck_scale (nu k) ((T (nu k)).list.node 0).2
    (T (nu k)).node_zero_readout.2.2
  apply (mul_le_mul_iff_right₀ (Real.sqrt_pos.mpr (H.base_scalar_pos (nu k)))).mp
  nlinarith only [hs, hzero]

end PoincareConjecture.M28.CounterexampleNeckFamily
