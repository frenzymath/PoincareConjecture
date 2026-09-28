import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceSelectedCrossingHeight
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceMatchingHighNeckSeparation
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeTerminalScalar
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.EmbeddingInverse











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

set_option maxHeartbeats 8000000 in





theorem exists_retained_source_crossing_height_accuracy :
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
                ∀ᶠ k in atTop,
                  Disjoint (range (fun z =>
                    ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.coordinate_map
                      (z, f k z))) (J k).central_sphere →
                  (∀ y ∈ (J k).central_sphere, y ∉
                    ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28
                      (f k)) ∧
                  ∃ height : (W.tube (W.high_index (G.subsequence (sigma k)))).carrierOpen → ℝ,
                    Continuous height ∧
                    (∀ y, height y = 0 ↔ y.val ∈ (J k).central_sphere) ∧
                    height (H.tubeBase W.tube
                      (W.high_index (G.subsequence (sigma k)))) < 0 ∧
                    0 < height (W.high_point (G.subsequence (sigma k))) := by
  classical
  obtain ⟨epsilonI, hIpos, _, hheight⟩ := exists_source_selected_crossing_height_accuracy.{u}
  obtain ⟨epsilonS, hSpos, hSsmall, hseparate⟩ :=
    exists_matching_high_neck_separation_accuracy.{u}
  obtain ⟨epsilonK, hKpos, _, hcompact⟩ :=
    exists_matching_high_neck_compact_exclusion_accuracy.{u}
  obtain ⟨epsilonT, hTpos, _, hterminal⟩ := exists_source_terminal_neck_exclusion_accuracy.{u}
  refine ⟨min epsilonI (min epsilonS (min epsilonK epsilonT)),
    lt_min hIpos (lt_min hSpos (lt_min hKpos hTpos)),
    ((min_le_right _ _).trans (min_le_left _ _)).trans hSsmall, ?_⟩
  intro epsilon C A E H W hepsilon G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D0 q sigma hsigma J heps hcenter f hf hbound hlabels
  have hepsI : epsilon ≤ epsilonI := hepsilon.trans (min_le_left _ _)
  have hepsS : epsilon ≤ epsilonS :=
    hepsilon.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hepsK : epsilon ≤ epsilonK :=
    hepsilon.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hepsT : epsilon ≤ epsilonT :=
    hepsilon.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let nu := fun k => W.high_index (G.subsequence (sigma k))
  have hnu : StrictMono nu := W.high_index_strictMono.comp
    (G.subsequence_strictMono.comp hsigma)
  obtain ⟨j, hjq⟩ : ∃ j, q ∈ G.exhaustion j := by
    have hq : q ∈ ⋃ j, G.exhaustion j := by rw [G.exhaustion_covers]; exact mem_univ _
    exact mem_iUnion.mp hq
  let K0 := closure (G.exhaustion j)
  have hK0 : IsCompact K0 := G.exhaustion_compactClosure j
  have hKconn : IsPreconnected K0 := (G.exhaustion_connected j).isPreconnected.closure
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun j => subset_closure.trans (G.exhaustion_step j))
  have hsep := hseparate H W hepsS G D0 q sigma hsigma J heps hcenter
  have hcomp := hcompact H W G D0 K0 hK0 sigma hsigma
  obtain ⟨B, _, hB⟩ := H.exists_eventual_compact_normalized_raw_scalar_bound
    W.tube W.radius W.radius_pos W.high_index G D0 {q} isCompact_singleton
  have hcenterB : ∀ᶠ k in atTop,
      (H.normalizedSliceConnection (nu k)).scalarCurvature (J k).center ≤ B := by
    filter_upwards [hsigma.tendsto_atTop.eventually hB] with k hk
    rw [hcenter]
    exact (le_abs_self _).trans (hk q (mem_singleton q))
  have hterm := hterminal H W.tube hepsT nu hnu J heps B hcenterB
  filter_upwards [hsep, hcomp, hterm, hlabels,
    hsigma.tendsto_atTop.eventually (eventually_ge_atTop (j + 1))]
    with k hksep hkcomp hkterm hklabels hkstage
  intro hSC
  let T := W.tube (nu k)
  have hcenterT : (J k).center ∈ (T.carrierOpen : Set _) := by
    rw [hcenter]
    exact (G.embedding (sigma k) q).val.property
  have hpT : (W.high_point (G.subsequence (sigma k))).val ∈
      (T.carrierOpen : Set _) := (W.high_point (G.subsequence (sigma k))).property
  rw [T.carrier_eq_iUnion_nodes] at hpT
  obtain ⟨i, hi, hp⟩ := mem_iUnion₂.mp hpT
  let P := (T.list.node (i : ℤ)).2
  have hactive : (i : ℤ) ∈ T.list.active := by
    have hi' := Finset.mem_range.mp hi
    change 0 ≤ (i : ℤ) ∧ (i : ℤ) ≤ (T.list.nodes.length : ℤ) - 1
    omega
  have hepsP : P.epsilon = epsilon := T.list.node_epsilon hactive
  obtain ⟨hP0, hPJ⟩ := hksep P (hepsP.trans_le hepsS) hp
  have hPK0 := hkcomp P (hepsP.trans_le hepsK) hp
  let K : Set T.carrierOpen := (fun x => (G.embedding (sigma k) x).val) '' K0
  have hKstage : K0 ⊆ G.exhaustion (sigma k) :=
    (G.exhaustion_step j).trans (hmono hkstage)
  have hmap : ContinuousOn (G.embedding (sigma k)) K0 := by
    intro x hx
    exact (G.embedding_smooth (sigma k) ⟨x, hKstage hx⟩).contMDiffAt.continuousAt.continuousWithinAt
  have hK : IsPreconnected K := hKconn.image _
    (continuous_subtype_val.comp_continuousOn hmap)
  have hbK : H.tubeBase W.tube (nu k) ∈ K := by
    refine ⟨G.base, subset_closure (G.base_in_exhaustion j), ?_⟩
    change (G.embedding (sigma k) G.base).val = H.tubeBase W.tube (nu k)
    rw [G.base_preserving]
    rfl
  have hqK : (⟨(J k).center, hcenterT⟩ : T.carrierOpen) ∈ K := by
    refine ⟨q, subset_closure hjq, ?_⟩
    exact Subtype.ext (hcenter k).symm
  have hPK : Disjoint P.carrier ((Subtype.val : T.carrierOpen → _) '' K) := by
    apply Set.disjoint_left.mpr
    rintro _ hxP ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hy
    exact Set.disjoint_left.mp hPK0 hxP ⟨z, hz, rfl⟩
  exact hheight T hepsI (f k) (hf k) (hbound k) (J k) (heps k) hcenterT
    hklabels.2 hkterm hSC i (Finset.mem_range.mp hi) hP0 hPJ
    (H.tubeBase W.tube (nu k)) (W.high_point (G.subsequence (sigma k)))
    hklabels.1 hp K hK hbK hqK hPK

end PoincareConjecture.M28.CounterexampleNeckFamily
