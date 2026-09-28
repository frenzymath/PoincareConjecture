import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallCrossingHeight
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeIntersectingSlab
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeCrossingMargin
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeSharpScalar
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallInitialRadius

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

set_option maxHeartbeats 3200000 in

theorem exists_retained_fresh_slab_radial_margin_accuracy :
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
          ∀ (_D0 : LeviCivitaData G.limitMetric) (q : G.limitCarrier.carrier)
            (sigma : ℕ → ℕ), StrictMono sigma →
            ∀ (J : ∀ k, EpsilonNeck
              ((E (W.high_index (G.subsequence (sigma k)) + H.shift)).flow.metric
                (E (W.high_index (G.subsequence (sigma k)) + H.shift)).time)),
              (∀ k, (J k).epsilon = epsilon) →
              (∀ k, (J k).center = (G.embedding (sigma k) q).val.val) →
              ∀ (f : ℕ → UnitTwoSphere → ℝ),
                (∀ k, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (f k)) →
                (∀ k z, |f k z| < epsilon⁻¹ / 32) →
                (∀ᶠ k in atTop,
                  (H.tubeBase W.tube (W.high_index (G.subsequence (sigma k)))).val ∈
                    range (fun z =>
                    ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.coordinate_map
                        (z, f k z)) ∧
                  (J k).center ∉
                    ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28
                      (f k)) →
                ∀ rmin : ℝ, 0 < rmin →
                  (∀ᶠ k in atTop, rmin ≤ Real.sqrt
                    ((E (W.high_index (G.subsequence (sigma k)) + H.shift)).flow.scalar
                      ⟨(E (W.high_index (G.subsequence (sigma k)) + H.shift)).time,
                        (E (W.high_index (G.subsequence (sigma k)) + H.shift)).basepoint⟩) *
                          (J k).scale) →
                  ∃ eta : ℝ, 0 < eta ∧ eta < W.radius ∧ ∀ᶠ k in atTop,
                    ∀ x ∈ (J k).carrier,
                      |((J k).coordinate_inverse x).2| ≤ 3 * epsilon⁻¹ / 4 →
                      ∃ hx : x ∈ (W.tube
                        (W.high_index (G.subsequence (sigma k)))).carrierOpen,
                        ((H.tubeMetric W.tube (W.high_index (G.subsequence (sigma k)))).edist
                          (H.tubeBase W.tube (W.high_index (G.subsequence (sigma k))))
                          ⟨x, hx⟩).toReal < W.radius - eta := by
  classical
  obtain ⟨epsilonC, hCpos, _, hcross⟩ := exists_retained_source_crossing_height_accuracy.{u}
  obtain ⟨epsilonS, hSpos, _, hseparate⟩ := exists_matching_high_neck_separation_accuracy.{u}
  obtain ⟨epsilonT, hTpos, _, hterminal⟩ := exists_source_terminal_neck_exclusion_accuracy.{u}
  obtain ⟨epsilonF, hFpos, _, hscale⟩ := exists_source_tube_fresh_scale_accuracy.{u}
  obtain ⟨epsilonR, hRpos, _, hradius⟩ := exists_retained_criticalBall_large_radius_accuracy.{u}
  refine ⟨min (1 / 10000) (min epsilonC (min epsilonS (min epsilonT
    (min epsilonF epsilonR)))),
    lt_min (by norm_num) (lt_min hCpos (lt_min hSpos (lt_min hTpos (lt_min hFpos hRpos)))),
    min_le_left _ _, ?_⟩
  intro epsilon C A E H W hepsilon G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D0 q sigma hsigma J heps hcenter f hf hbound hlabels rmin hrmin hfloor
  have hepsSmall : epsilon ≤ (1 / 10000 : ℝ) := hepsilon.trans (min_le_left _ _)
  have hepsRest := hepsilon.trans (min_le_right _ _)
  have hepsC : epsilon ≤ epsilonC := hepsRest.trans (min_le_left _ _)
  have hepsRest' := hepsRest.trans (min_le_right _ _)
  have hepsS : epsilon ≤ epsilonS := hepsRest'.trans (min_le_left _ _)
  have hepsRest'' := hepsRest'.trans (min_le_right _ _)
  have hepsT : epsilon ≤ epsilonT := hepsRest''.trans (min_le_left _ _)
  have hepsF : epsilon ≤ epsilonF :=
    hepsRest''.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hepsR : epsilon ≤ epsilonR :=
    hepsRest''.trans ((min_le_right _ _).trans (min_le_right _ _))
  let nu := fun k => W.high_index (G.subsequence (sigma k))
  let s0 : ℝ := (4 * max C 2)⁻¹
  have hA : 0 < epsilon⁻¹ := inv_pos.mpr ((heps 0) ▸ (J 0).epsilon_pos)
  have hB : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right C 2)
  have hs0 : 0 < s0 := by dsimp only [s0]; positivity
  have hlarge : (7 / 4 : ℝ) * s0 * epsilon⁻¹ ≤ W.radius := hradius H hepsR W
  let eta : ℝ := min (s0 * epsilon⁻¹ / 8) (3 * rmin * epsilon⁻¹ / 32) / 2
  have hmin : 0 < min (s0 * epsilon⁻¹ / 8) (3 * rmin * epsilon⁻¹ / 32) := by positivity
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have heta1 : eta < s0 * epsilon⁻¹ / 8 := (half_lt_self hmin).trans_le (min_le_left _ _)
  have heta2 : eta < 3 * rmin * epsilon⁻¹ / 32 :=
    (half_lt_self hmin).trans_le (min_le_right _ _)
  refine ⟨eta, heta, by nlinarith only [heta1, hlarge, mul_pos hs0 hA], ?_⟩
  have hcrossTail := hcross H W hepsC G D0 q sigma hsigma J heps hcenter f hf hbound hlabels
  have hsep := hseparate H W hepsS G D0 q sigma hsigma J heps hcenter
  have hnu : StrictMono nu := W.high_index_strictMono.comp
    (G.subsequence_strictMono.comp hsigma)
  obtain ⟨B, _, hBsource⟩ := H.exists_eventual_compact_normalized_raw_scalar_bound
    W.tube W.radius W.radius_pos W.high_index G D0 {q} isCompact_singleton
  have hcenterB : ∀ᶠ k in atTop,
      (H.normalizedSliceConnection (nu k)).scalarCurvature (J k).center ≤ B := by
    filter_upwards [hsigma.tendsto_atTop.eventually hBsource] with k hk
    rw [hcenter]
    exact (le_abs_self _).trans (hk q (mem_singleton q))
  have hterm := hterminal H W.tube hepsT nu hnu J heps B hcenterB
  have herror : ∀ᶠ k in atTop,
      1 / ((G.subsequence (sigma k) : ℝ) + 1) < rmin * epsilon⁻¹ / 32 :=
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (G.subsequence_strictMono.comp hsigma).tendsto_atTop).eventually
        (gt_mem_nhds (by positivity))
  filter_upwards [hcrossTail, hsep, hterm, hlabels, hfloor, herror]
    with k hkcross hksep hkterm hklabels hkfloor hkerror
  let T := W.tube (nu k)
  have hcenterT : (J k).center ∈ (T.carrierOpen : Set _) := by
    rw [hcenter]
    exact (G.embedding (sigma k) q).val.property
  have hscaleK : (J k).scale ≤ (101 / 100 : ℝ) * (T.list.node 0).2.scale := by
    have hh := hscale H W.tube hepsF (nu k) (J k) hcenterT
    have hzero := H.normalizedSlice_low_neck_scale (nu k) (T.list.node 0).2
      T.node_zero_readout.2.2
    apply (mul_le_mul_iff_left₀ (Real.sqrt_pos.mpr (H.base_scalar_pos (nu k)))).mp
    nlinarith only [hh, hzero]
  have hslab := T.fresh_three_quarter_slab_subset hepsSmall (f k) (hf k).continuous
    (hbound k) (J k) (heps k) hscaleK hcenterT hklabels.2 hkterm
  intro x hx hheight
  have hxT : x ∈ T.carrierOpen := by
    apply hslab
    exact ⟨(J k).coordinate_inverse x, ⟨mem_univ _, abs_le.mp hheight⟩,
      (J k).coordinate_map_coordinate_inverse hx⟩
  refine ⟨hxT, ?_⟩
  let xU : T.carrierOpen := ⟨x, hxT⟩
  by_cases hdisjoint : Disjoint
      (range (fun z => (T.list.node 0).2.coordinate_map (z, f k z))) (J k).central_sphere
  · obtain ⟨hsideAll, height, hcont, hzero, hb, hp⟩ := hkcross hdisjoint
    have hpT : (W.high_point (G.subsequence (sigma k))).val ∈
        (T.carrierOpen : Set _) := (W.high_point (G.subsequence (sigma k))).property
    rw [T.carrier_eq_iUnion_nodes] at hpT
    obtain ⟨i, hi, hpP⟩ := mem_iUnion₂.mp hpT
    have hactive : (i : ℤ) ∈ T.list.active := by
      have hi' := Finset.mem_range.mp hi
      change 0 ≤ (i : ℤ) ∧ (i : ℤ) ≤ (T.list.nodes.length : ℤ) - 1
      omega
    have hPJ := (hksep (T.list.node (i : ℤ)).2
      ((T.list.node_epsilon hactive).trans_le hepsS) hpP).2
    have hpnot : (W.high_point (G.subsequence (sigma k))).val ∉ (J k).carrier :=
      fun hh => Set.disjoint_left.mp hPJ hpP hh
    have hgain := H.tube_edist_add_le_of_fresh_sphere_height W.tube (nu k)
      hepsSmall (f k) (hf k).continuous (hbound k) (J k) (heps k) hscaleK hkterm
      (W.high_point (G.subsequence (sigma k))) xU hx hheight hpnot hsideAll
      height hcont hzero hb hp
    have hreal := ENNReal.toReal_mono
      (H.tube_edist_ne_top W.tube (nu k) _ _) hgain
    have hNscale := (J k).scale_pos
    rw [ENNReal.toReal_add (H.tube_edist_ne_top W.tube (nu k) _ _)
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by positivity)] at hreal
    have hfloorA := mul_le_mul_of_nonneg_right hkfloor hA.le
    have hpupper := W.high_radius_upper (G.subsequence (sigma k))
    nlinarith only [hreal, hfloorA, hpupper, hkerror, heta2]
  · have hmeet := Set.not_disjoint_iff_nonempty_inter.mp hdisjoint
    have hshort := H.tube_distance_lt_of_initial_graph_intersection W.tube (nu k)
      hepsSmall (f k) (hf k).continuous (hbound k) (J k) (heps k) hscaleK hkterm
      hmeet xU hx hheight
    have hreal := ENNReal.toReal_lt_of_lt_ofReal hshort
    nlinarith only [hreal, hlarge, heta1]

end PoincareConjecture.M28.CounterexampleNeckFamily
