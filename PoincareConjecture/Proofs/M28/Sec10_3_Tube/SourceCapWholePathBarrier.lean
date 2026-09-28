import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceNeckRegion
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CapScalarBand











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28





theorem exists_source_cap_whole_path_avoidance_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ {epsilon C A D₀ D : ℝ} (E : SameTimeCounterexample.{u} epsilon C A D₀ D)
        (S : CounterexampleNeckSegment E),
        0 < E.flow.scalar ⟨E.time, E.basepoint⟩ → epsilon ≤ epsilon₀ →
        ∀ K : CapCertificate (E.flow.metric E.time), K.epsilon = epsilon →
          K.cap_constant ≤ C → ∀ x ∈ S.neckCarrierUnion, x ∈ K.carrier →
            K.carrier ⊆ S.source_region.cover.X ∧
              S.path 0 ∉ K.carrier ∧ S.path 1 ∉ K.carrier ∧
              Disjoint K.closed_core (S.path '' Icc (0 : ℝ) 1) := by
  obtain ⟨epsilonR, hRpos, hRsmall, hregion⟩ :=
    exists_source_neck_region_accuracy.{u}
  let epsilon₀ := min epsilonR neckShorteningEpsilon
  refine ⟨epsilon₀, lt_min hRpos neckShorteningEpsilon_pos,
    (min_le_left _ _).trans hRsmall, ?_⟩
  intro epsilon C A D₀ D E S hQ hsmall K hepsilon hKC x hx hxK
  obtain ⟨hcomponent, _, hbounds⟩ :=
    hregion E S hQ (hsmall.trans (min_le_left _ _))
  obtain ⟨hlow, hhigh⟩ := hbounds x hx
  let B := max C 2
  let Q := E.flow.scalar ⟨E.time, E.basepoint⟩
  have hB : 2 ≤ B := le_max_right C 2
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hKB : K.cap_constant ≤ B := hKC.trans (le_max_left C 2)
  have hBsq : 2 * B ≤ B ^ 2 := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hB hBpos.le
  have hBsqQ := mul_le_mul_of_nonneg_right hBsq hQ.le
  have hlow' : 16 * B * Q ≤ (E.flow.connection E.time).scalarCurvature x := by
    change 16 * B * Q ≤ E.flow.scalar ⟨E.time, x⟩
    nlinarith only [hlow, hBsqQ]
  have hcap : K.carrier ⊆ S.source_region.cover.X := by
    have hsub := K.carrier_subset_scalar_component
      (E.flow.connection E.time) hKB hQ hxK hlow'
    change K.carrier ⊆ connectedComponentIn
      {p | 4 * Q < E.flow.scalar ⟨E.time, p⟩} x at hsub
    have heq := connectedComponentIn_eq
      (S.source_region.cover_set ▸ hcomponent hx)
    rw [← heq, ← S.source_region.cover_set] at hsub
    exact hsub
  have hstart : S.path 0 ∉ K.carrier := by
    intro hmem
    have hratio := K.scalar_lt_mul (E.flow.connection E.time) hKB hmem hxK
    change E.flow.scalar ⟨E.time, x⟩ < B * E.flow.scalar ⟨E.time, S.path 0⟩
      at hratio
    have hscale := mul_le_mul_of_nonneg_left S.source_region.lower_scalar hBpos.le
    nlinarith only [hratio, hscale, hlow]
  have hend : S.path 1 ∉ K.carrier := by
    intro hmem
    have hratio := K.scalar_lt_mul (E.flow.connection E.time) hKB hxK hmem
    change E.flow.scalar ⟨E.time, S.path 1⟩ < B * E.flow.scalar ⟨E.time, x⟩
      at hratio
    have hcut : E.flow.scalar ⟨E.time, S.path S.upper⟩ * (2 * B) =
        E.flow.scalar ⟨E.time, S.path 1⟩ := by
      rw [S.upper_scalar_eq]
      exact div_mul_cancel₀ _ (mul_pos (by norm_num) hBpos).ne'
    have hscale := mul_le_mul_of_nonneg_left hhigh hBpos.le
    nlinarith only [hratio, hcut, hscale]
  refine ⟨hcap, hstart, hend, ?_⟩
  apply disjoint_left.mpr
  rintro y hycore ⟨t, ht, rfl⟩
  have hshort : K.epsilon ≤ neckShorteningEpsilon := by
    rw [hepsilon]
    exact hsmall.trans (min_le_right _ _)
  rcases K.endpoint_mem_of_intrinsic_minimizer hshort
      (hcap.trans S.source_region.cover_subset) ht S.path_smooth
      S.source_region.path_mem S.source_region.finite_length
      S.source_region.minimizing hycore with hzero | hone
  · exact hstart hzero
  · exact hend hone

end PoincareConjecture.M28
