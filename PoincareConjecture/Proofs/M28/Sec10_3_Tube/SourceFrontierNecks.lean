import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceNeckRegion
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceNecks












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28





theorem exists_source_closure_necks_accuracy (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A D₀ D : ℝ} (E : SameTimeCounterexample.{u} epsilon C A D₀ D)
        (S : CounterexampleNeckSegment E),
        0 < E.flow.scalar ⟨E.time, E.basepoint⟩ → epsilon ≤ epsilon₀ →
        ∀ N ∈ S.cover.necks,
          S.path 0 ∉ closure N.carrier ∧ S.path 1 ∉ closure N.carrier ∧
          ∀ t ∈ Icc (0 : ℝ) 1, S.path t ∈ closure N.carrier →
            ∃ J : GeneralizedStrongNeck E.flow E.time epsilon,
              J.center = S.path t ∧
              let W := strongNeck_top J S.epsilon_lt_half
              W.carrier ⊆ S.source_region.cover.X ∧
                S.path 0 ∉ W.carrier ∧ S.path 1 ∉ W.carrier ∧
                ∀ p ∈ W.carrier,
                  9 * (max C 2) ^ 2 * E.flow.scalar ⟨E.time, E.basepoint⟩ ≤
                    E.flow.scalar ⟨E.time, p⟩ ∧
                  E.flow.scalar ⟨E.time, p⟩ ≤
                    (25 / 16 : ℝ) * E.flow.scalar ⟨E.time, S.path S.upper⟩ := by
  obtain ⟨epsilonS, hSpos, _, hscalar⟩ :=
    tube.exists_cylinder_scalar_accuracy.{u} (delta := 1 / 4) (by norm_num)
  obtain ⟨epsilonC, hCpos, _, hcompact⟩ :=
    exists_claim10_4_compact_exclusion_accuracy P
  let epsilon₀ := min epsilonS (min epsilonC (min neckShorteningEpsilon (1 / 1000)))
  refine ⟨epsilon₀,
    lt_min hSpos (lt_min hCpos (lt_min neckShorteningEpsilon_pos (by norm_num))),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)), ?_⟩
  intro epsilon C A D₀ D E S hQ hsmall N hN
  let R : (E.flow.slice E.time).carrier → ℝ := fun p => E.flow.scalar ⟨E.time, p⟩
  let Q := R E.basepoint
  let B := max C 2
  have hB : 2 ≤ B := le_max_right C 2
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hBQ : 0 < B * Q := mul_pos hBpos hQ
  have hBsq : 2 * B ≤ B ^ 2 := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hB hBpos.le
  have hBsqQ := mul_le_mul_of_nonneg_right hBsq hQ.le
  have hBQge := mul_le_mul_of_nonneg_right hB hQ.le
  have hsmallS : epsilon ≤ epsilonS := hsmall.trans (min_le_left _ _)
  have hsmallC : epsilon ≤ epsilonC :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hshort : epsilon ≤ neckShorteningEpsilon :=
    hsmall.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hcontinuous : Continuous R := E.flow.continuous_scalar_slice P E.time
  have hclosure (W : EpsilonNeck (E.flow.metric E.time))
      (hW : W.epsilon ≤ epsilonS) :
      ∀ p ∈ closure W.carrier,
        (3 / 4 : ℝ) * R W.center ≤ R p ∧ R p ≤ (5 / 4 : ℝ) * R W.center := by
    have hnorm := tube.neck_normalized_scalar_center W (E.flow.connection E.time)
    change W.scale ^ 2 * R W.center = 1 at hnorm
    have hscale : 0 < W.scale ^ 2 := pow_pos W.scale_pos 2
    have hpoint : W.carrier ⊆ {p | (3 / 4 : ℝ) * R W.center ≤ R p ∧
        R p ≤ (5 / 4 : ℝ) * R W.center} := by
      intro p hp
      have herr := abs_lt.mp (hscalar (E.flow.slice E.time).carrier
        (E.flow.metric E.time) (E.flow.connection E.time) W hW p hp)
      change -(1 / 4 : ℝ) < W.scale ^ 2 * R p - 1 ∧
        W.scale ^ 2 * R p - 1 < 1 / 4 at herr
      constructor
      · apply (mul_le_mul_iff_right₀ hscale).mp
        nlinarith only [herr.1, hnorm]
      · apply (mul_le_mul_iff_right₀ hscale).mp
        nlinarith only [herr.2, hnorm]
    exact closure_minimal hpoint
      ((isClosed_le continuous_const hcontinuous).inter
        (isClosed_le hcontinuous continuous_const))
  have hNepsilon : N.epsilon = epsilon :=
    (S.cover.neck_epsilon N hN).trans S.cover_epsilon
  have hNsmall : N.epsilon ≤ epsilonS := by
    rw [hNepsilon]
    exact hsmallS
  have hcenter := S.center_mem_cover N hN
  rw [S.cover_set] at hcenter
  obtain ⟨c, hc, hcenter⟩ := hcenter
  have hcenterBand := S.scalar_band c hc
  rw [hcenter] at hcenterBand
  have hNscalar (p : (E.flow.slice E.time).carrier) (hp : p ∈ closure N.carrier) :
      12 * B ^ 2 * Q ≤ R p ∧ R p ≤ (5 / 4 : ℝ) * R (S.path S.upper) := by
    have h := hclosure N hNsmall p hp
    constructor <;> nlinarith only [h.1, h.2, hcenterBand.1, hcenterBand.2]
  have hcenterPos : 0 < R N.center := by
    change 0 < (E.flow.connection E.time).scalarCurvature N.center
    rw [← N.connection.scalarCurvature_eq_m28 (E.flow.connection E.time)]
    exact N.scalar_center_pos
  have hupperPos : 0 < R (S.path S.upper) := hcenterPos.trans_le hcenterBand.2
  have hcut : R (S.path S.upper) * (2 * B) = R (S.path 1) := by
    change E.flow.scalar ⟨E.time, S.path S.upper⟩ * (2 * B) = _
    rw [S.upper_scalar_eq]
    exact div_mul_cancel₀ _ (mul_pos (by norm_num) hBpos).ne'
  have hupperB := mul_le_mul_of_nonneg_right hB hupperPos.le
  have hstartOut : S.path 0 ∉ closure N.carrier := by
    intro hp
    have hlo := (hNscalar _ hp).1
    nlinarith only [hlo, S.source_region.lower_scalar, hBsqQ, hBQ]
  have hendOut : S.path 1 ∉ closure N.carrier := by
    intro hp
    have hhi := (hNscalar _ hp).2
    nlinarith only [hhi, hcut, hupperB, hupperPos]
  have hNcomponent : closure N.carrier ⊆ S.source_region.cover.X := by
    have hcN := subset_closure (N.central_sphere_subset N.center_on_central_sphere)
    have hsuper : closure N.carrier ⊆ {p | 4 * Q < R p} := by
      intro p hp
      have hlow := (hNscalar p hp).1
      change 4 * Q < R p
      nlinarith only [hlow, hBsqQ, hBQge, hQ]
    have hsub := N.isPreconnected_carrier.closure.subset_connectedComponentIn hcN hsuper
    have heq := connectedComponentIn_eq (S.source_region.cover_set ▸
      S.cover_subset_component (S.center_mem_cover N hN))
    rw [← heq, ← S.source_region.cover_set] at hsub
    exact hsub
  have hC : 0 < C := by
    rw [← S.source_region.cover_constant]
    exact S.source_region.cover.cap_constant_pos
  have hstart' : R (S.path 0) ≤ 8 * (B * Q) := by
    simpa only [mul_assoc] using S.source_region.lower_scalar
  have hend' : 32 * (max C 2) ^ 2 * (B * Q) < R (S.path 1) := by
    calc
      _ = 32 * B ^ 3 * Q := by ring
      _ < _ := S.source_region.upper_scalar
  obtain ⟨hcomponent, hround⟩ := hcompact E.flow E.time epsilon C (B * Q)
    hsmallC hC hBQ S.path 0 1 zero_le_one S.path_smooth.continuousOn hstart' hend'
  refine ⟨hstartOut, hendOut, ?_⟩
  intro t ht htN
  have htComponent := hNcomponent htN
  have htBand := hNscalar _ htN
  have hcan : Nonempty
      (GeneralizedCanonicalControl (F := E.flow) E.time (S.path t) epsilon C) := by
    apply E.canonical
    change 4 * Q ≤ R (S.path t)
    nlinarith only [htBand.1, hBsqQ, hBQge, hQ]
  obtain ⟨hcan⟩ := hcan
  cases hcan with
  | neck J hJ =>
    refine ⟨J, hJ, ?_⟩
    let W := strongNeck_top J S.epsilon_lt_half
    have hWcenter : W.center = S.path t := hJ
    have hWscalar (p : (E.flow.slice E.time).carrier) (hp : p ∈ W.carrier) :
        9 * B ^ 2 * Q ≤ R p ∧ R p ≤ (25 / 16 : ℝ) * R (S.path S.upper) := by
      have h := hclosure W hsmallS p (subset_closure hp)
      rw [hWcenter] at h
      constructor <;> nlinarith only [h.1, h.2, htBand.1, htBand.2]
    have hWcomponent : W.carrier ⊆ S.source_region.cover.X := by
      have hcW := W.central_sphere_subset W.center_on_central_sphere
      have hsuper : W.carrier ⊆ {p | 4 * Q < R p} := by
        intro p hp
        have hlow := (hWscalar p hp).1
        change 4 * Q < R p
        nlinarith only [hlow, hBsqQ, hBQge, hQ]
      have hsub := W.isPreconnected_carrier.subset_connectedComponentIn hcW hsuper
      rw [hWcenter] at hsub
      have heq := connectedComponentIn_eq (S.source_region.cover_set ▸ htComponent)
      rw [← heq, ← S.source_region.cover_set] at hsub
      exact hsub
    refine ⟨hWcomponent, ?_, ?_, hWscalar⟩
    · intro hp
      have hlo := (hWscalar _ hp).1
      nlinarith only [hlo, S.source_region.lower_scalar, hBsqQ, hBQ]
    · intro hp
      have hhi := (hWscalar _ hp).2
      nlinarith only [hhi, hcut, hupperB, hupperPos]
  | cap K hepsilon hKC _hconnection hcore =>
    exfalso
    have htK := K.core_subset_carrier_m28 hcore
    have hKB : K.cap_constant ≤ B := hKC.trans (le_max_left C 2)
    have hlow : 16 * B * Q ≤ (E.flow.connection E.time).scalarCurvature (S.path t) := by
      change 16 * B * Q ≤ R (S.path t)
      nlinarith only [htBand.1, hBsqQ, hBQ]
    have hcap := K.carrier_subset_scalar_component
      (E.flow.connection E.time) hKB hQ htK hlow
    change K.carrier ⊆ connectedComponentIn {p | 4 * Q < R p} (S.path t) at hcap
    have heq := connectedComponentIn_eq (S.source_region.cover_set ▸ htComponent)
    rw [← heq, ← S.source_region.cover_set] at hcap
    have hstart : S.path 0 ∉ K.carrier := by
      intro hp
      have hr := K.scalar_lt_mul (E.flow.connection E.time) hKB hp htK
      change R (S.path t) < B * R (S.path 0) at hr
      have hscale := mul_le_mul_of_nonneg_left S.source_region.lower_scalar hBpos.le
      nlinarith only [hr, hscale, htBand.1, hBsqQ, hBQ]
    have hend : S.path 1 ∉ K.carrier := by
      intro hp
      have hr := K.scalar_lt_mul (E.flow.connection E.time) hKB htK hp
      change R (S.path 1) < B * R (S.path t) at hr
      have hscale := mul_le_mul_of_nonneg_left htBand.2 hBpos.le
      have hprod := mul_pos hBpos hupperPos
      nlinarith only [hr, hscale, hcut, hprod]
    have hclosed : S.path t ∈ K.closed_core := by
      rw [K.core_eq_interior_closed_core] at hcore
      exact interior_subset hcore
    rcases K.endpoint_mem_of_intrinsic_minimizer
        (by simpa only [hepsilon] using hshort)
        (hcap.trans S.source_region.cover_subset) ht S.path_smooth
        S.source_region.path_mem S.source_region.finite_length
        S.source_region.minimizing hclosed with hzero | hone
    · exact hstart hzero
    · exact hend hone
  | component K hK =>
    exact (disjoint_left.mp (hcomponent K) (mem_image_of_mem S.path ht) hK).elim
  | round K hK =>
    exact (disjoint_left.mp (hround K) (mem_image_of_mem S.path ht) hK).elim

end PoincareConjecture.M28
