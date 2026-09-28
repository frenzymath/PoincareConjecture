import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeCapExclusion
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceNecks

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

theorem exists_source_tube_centered_strong_necks_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A D₀ D : ℝ} (E : SameTimeCounterexample.{u} epsilon C A D₀ D)
        (S : CounterexampleNeckSegment E),
        0 < E.flow.scalar ⟨E.time, E.basepoint⟩ → epsilon ≤ epsilon₀ →
        ∀ T : SourceTubeData S, ∀ x ∈ (T.carrierOpen : Set _),
          ∃ J : GeneralizedStrongNeck E.flow E.time epsilon, J.center = x := by
  obtain ⟨epsilonK, hKpos, hKsmall, hcap⟩ := exists_source_tube_cap_exclusion_accuracy P
  obtain ⟨epsilonC, hCpos, _, hcompact⟩ := exists_claim10_4_compact_exclusion_accuracy P
  obtain ⟨epsilonR, hRpos, _, hregion⟩ := exists_source_neck_region_accuracy.{u}
  let epsilon₀ := min epsilonK (min epsilonC epsilonR)
  refine ⟨epsilon₀, lt_min hKpos (lt_min hCpos hRpos),
    (min_le_left _ _).trans hKsmall, ?_⟩
  intro epsilon C A D₀ D E S hQ hsmall T x hxT
  have hεK : epsilon ≤ epsilonK := hsmall.trans (min_le_left _ _)
  have hεC : epsilon ≤ epsilonC :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεR : epsilon ≤ epsilonR :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  let Q := E.flow.scalar ⟨E.time, E.basepoint⟩
  let B := max C 2
  have hB : 2 ≤ B := le_max_right C 2
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hC : 0 < C := by
    rw [← S.source_region.cover_constant]
    exact S.source_region.cover.cap_constant_pos
  have hstart : E.flow.scalar ⟨E.time, S.path 0⟩ ≤ 8 * (B * Q) := by
    simpa only [mul_assoc] using S.source_region.lower_scalar
  have hend : 32 * (max C 2) ^ 2 * (B * Q) <
      E.flow.scalar ⟨E.time, S.path 1⟩ := by
    calc
      _ = 32 * (max C 2) ^ 3 * Q := by dsimp only [B]; ring
      _ < _ := S.source_region.upper_scalar
  obtain ⟨hcomponent, hround⟩ := hcompact E.flow E.time epsilon C (B * Q)
    hεC hC (mul_pos hBpos hQ) S.path 0 1 zero_le_one S.path_smooth.continuousOn
    hstart hend
  have hT : IsPreconnected T.tube.carrier :=
    isPreconnected_iff_preconnectedSpace.mpr T.preconnected
  have hlowT : S.path S.lower ∈ (T.carrierOpen : Set _) :=
    T.path_mem (left_mem_Icc.mpr S.lower_lt_upper.le)
  have hlowPath : S.path S.lower ∈ S.path '' Icc (0 : ℝ) 1 :=
    mem_image_of_mem S.path
      ⟨S.lower_pos.le, (S.lower_lt_upper.trans S.upper_lt_one).le⟩
  have hscalar := ((hregion E S hQ hεR).2.2 x
    (T.carrier_subset_neckCarrierUnion hxT)).1
  have hcanonical : Nonempty
      (GeneralizedCanonicalControl (F := E.flow) E.time x epsilon C) := by
    apply E.canonical
    have hBsq : 1 ≤ B ^ 2 := by nlinarith only [hB]
    have h := mul_le_mul_of_nonneg_right hBsq hQ.le
    change 4 * Q ≤ E.flow.scalar ⟨E.time, x⟩
    nlinarith only [hscalar, h, hQ]
  obtain ⟨hcanonical⟩ := hcanonical
  cases hcanonical with
  | neck J hJ => exact ⟨J, hJ⟩
  | cap K hepsilon hKC _hconnection hxK =>
    exfalso
    have hxclosed : x ∈ K.closed_core := by
      rw [K.core_eq_interior_closed_core] at hxK
      exact interior_subset hxK
    exact disjoint_left.mp (hcap E S hQ hεK T K hepsilon hKC) hxclosed hxT
  | component K hxK =>
    exfalso
    have hsub : (T.carrierOpen : Set _) ⊆ K.carrier := by
      rw [K.component_eq] at hxK ⊢
      rw [connectedComponent_eq hxK]
      exact hT.subset_connectedComponent hxT
    exact disjoint_left.mp (hcomponent K) hlowPath (hsub hlowT)
  | round K hxK =>
    exfalso
    have hsub : (T.carrierOpen : Set _) ⊆ K.carrier := by
      rw [K.component_eq] at hxK ⊢
      rw [connectedComponent_eq hxK]
      exact hT.subset_connectedComponent hxT
    exact disjoint_left.mp (hround K) hlowPath (hsub hlowT)

end PoincareConjecture.M28
