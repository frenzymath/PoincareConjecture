import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceNecks













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M28





theorem exists_counterexample_superlevel_cover_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (epsilon C A D₀ D : ℝ), 0 < epsilon → epsilon ≤ epsilon₀ →
        0 < C → 0 < D₀ → 32 * (max C 2) ^ 2 ≤ D →
        ∀ E : SameTimeCounterexample.{u} epsilon C A D₀ D,
          let Q := E.flow.scalar ⟨E.time, E.basepoint⟩
          ∃ S : CounterexamplePathSegment E, ∃ c : ℝ,
            ∃ H : ConnectedNeckCapCover (E.flow.metric E.time),
              S.level_parameter < c ∧ c < 1 ∧
              E.flow.scalar ⟨E.time, S.path c⟩ = 8 * Q ∧
              H.X = connectedComponentIn
                {p | 4 * Q < E.flow.scalar ⟨E.time, p⟩} (S.path c) ∧
              H.epsilon = epsilon ∧ H.cap_constant = C ∧
              MapsTo S.path (Icc c 1) H.X ∧
              (E.flow.metric E.time).pathELength S.path c 1 <
                ENNReal.ofReal (A * Q ^ (-1 / 2 : ℝ)) ∧
              ∃ hhalf : epsilon < 1 / 2,
                ∀ N ∈ H.necks, ∃ J : GeneralizedStrongNeck E.flow E.time epsilon,
                  N = strongNeck_top J hhalf ∧ J.center ∈ H.X := by
  obtain ⟨epsilon₀, hpos, hthreshold, hexclude⟩ :=
    exists_claim10_4_compact_exclusion_accuracy P
  refine ⟨epsilon₀, hpos, hthreshold, ?_⟩
  intro epsilon C A D₀ D hepsilon hsmall hC hD₀ hD E
  dsimp only
  let Q := E.flow.scalar ⟨E.time, E.basepoint⟩
  have hQ : 0 < Q := lt_of_lt_of_le hD₀ E.base_lower
  have hB : 2 ≤ max C 2 := le_max_right C 2
  have hBsquare : 4 ≤ (max C 2) ^ 2 := by
    nlinarith only [hB, sq_nonneg (max C 2 - 2)]
  have hD8 : 8 ≤ D := by nlinarith only [hD, hBsquare]
  obtain ⟨S⟩ := exists_counterexample_path_segment P E hD₀
    ((by norm_num : (4 : ℝ) ≤ 8).trans hD8)
  obtain ⟨c, hbefore, hlast, hlevel, _, hpath, hlength, hcanonical⟩ :=
    CounterexamplePathSegment.exists_level_eight_suffix P S hD₀ hD8
  let X := connectedComponentIn {p | 4 * Q < E.flow.scalar ⟨E.time, p⟩} (S.path c)
  have hlevel' : E.flow.scalar ⟨E.time, S.path c⟩ = 8 * Q := hlevel
  have hX : IsConnected X := by
    apply isConnected_connectedComponentIn_iff.mpr
    change 4 * Q < E.flow.scalar ⟨E.time, S.path c⟩
    linarith only [hlevel', hQ]
  have hxX : S.path c ∈ X := hpath (left_mem_Icc.mpr hlast.le)
  have hend : 32 * (max C 2) ^ 2 * Q < E.flow.scalar ⟨E.time, S.path 1⟩ := by
    have hbound : 32 * (max C 2) ^ 2 * Q ≤ D * Q :=
      mul_le_mul_of_nonneg_right hD hQ.le
    exact hbound.trans_lt (by simpa only [Q, S.path_one] using E.scalar_large)
  obtain ⟨hcomponentPath, hroundPath⟩ :=
    hexclude E.flow E.time epsilon C Q hsmall hC hQ S.path c 1 hlast.le
      S.path_smooth.continuous.continuousOn hlevel'.le hend
  have hpathStart : S.path c ∈ S.path '' Icc c 1 :=
    mem_image_of_mem S.path (left_mem_Icc.mpr hlast.le)
  have hcomponent (N : SingularCComponent (E.flow.metric E.time)
      (E.flow.connection E.time) C) : Disjoint X N.carrier := by
    apply disjoint_left.mpr
    intro x hx hxN
    have hsub : X ⊆ N.carrier :=
      N.preconnected_subset hX.isPreconnected ⟨x, hx, hxN⟩
    exact disjoint_left.mp (hcomponentPath N) hpathStart (hsub hxX)
  have hround (N : SingularRoundComponent (E.flow.metric E.time) epsilon) :
      Disjoint X N.carrier := by
    apply disjoint_left.mpr
    intro x hx hxN
    have hsub : X ⊆ N.carrier := by
      rw [N.component_eq] at hxN ⊢
      rw [connectedComponent_eq hxN]
      exact hX.isPreconnected.subset_connectedComponent hx
    exact disjoint_left.mp (hroundPath N) hpathStart (hsub hxX)
  let H := testedSliceNeckCapCover hepsilon hsmall hthreshold hC
    X hX hcanonical hcomponent hround
  have hhalf : epsilon < 1 / 2 :=
    lt_of_le_of_lt (hsmall.trans hthreshold) (by norm_num)
  refine ⟨S, c, H, hbefore, hlast, hlevel, rfl, rfl, rfl, hpath, hlength, hhalf, ?_⟩
  intro N hN
  exact testedSliceNeckCapCover_neck_provenance hepsilon hsmall hthreshold hC
    X hX hcanonical hcomponent hround N hN

end PoincareConjecture.M28
