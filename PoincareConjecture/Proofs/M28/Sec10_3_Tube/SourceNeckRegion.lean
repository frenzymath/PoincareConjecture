import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceFamilySelection











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckSegment

variable {epsilon C A D₀ D : ℝ}
  {E : SameTimeCounterexample.{u} epsilon C A D₀ D}



def neckCarrierUnion (S : CounterexampleNeckSegment E) :
    Set (E.flow.slice E.time).carrier :=
  {x | ∃ N ∈ S.cover.necks, x ∈ N.carrier}



theorem center_mem_cover (S : CounterexampleNeckSegment E)
    (N : EpsilonNeck (E.flow.metric E.time)) (hN : N ∈ S.cover.necks) :
    N.center ∈ S.cover.X := by
  obtain ⟨J, rfl, hcenter⟩ := S.provenance N hN
  exact hcenter


theorem cover_subset_neckCarrierUnion (S : CounterexampleNeckSegment E) :
    S.cover.X ⊆ S.neckCarrierUnion := by
  intro x hx
  obtain ⟨N, hN, hcenter⟩ := S.cover.pointwise_center_cover x hx
  exact ⟨N, hN, hcenter ▸ N.central_sphere_subset N.center_on_central_sphere⟩


theorem neckCarrierUnion_open (S : CounterexampleNeckSegment E) :
    IsOpen S.neckCarrierUnion := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨N, hN, hx⟩
  exact Filter.mem_of_superset (N.carrier_open.mem_nhds hx)
    (fun y hy => ⟨N, hN, hy⟩)



theorem neckCarrierUnion_connected (S : CounterexampleNeckSegment E) :
    IsConnected S.neckCarrierUnion := by
  obtain ⟨x, hx⟩ := S.cover.connected_X.nonempty
  refine ⟨⟨x, S.cover_subset_neckCarrierUnion hx⟩, ?_⟩
  apply isPreconnected_of_forall x
  rintro y ⟨N, hN, hy⟩
  refine ⟨S.cover.X ∪ N.carrier,
    union_subset S.cover_subset_neckCarrierUnion (fun z hz => ⟨N, hN, hz⟩),
    Or.inl hx, Or.inr hy, ?_⟩
  exact S.cover.connected_X.isPreconnected.union N.center (S.center_mem_cover N hN)
    (N.central_sphere_subset N.center_on_central_sphere) N.isPreconnected_carrier

end CounterexampleNeckSegment




theorem exists_source_neck_region_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ {epsilon C A D₀ D : ℝ} (E : SameTimeCounterexample.{u} epsilon C A D₀ D)
        (S : CounterexampleNeckSegment E),
        0 < E.flow.scalar ⟨E.time, E.basepoint⟩ → epsilon ≤ epsilon₀ →
        S.neckCarrierUnion ⊆ S.source_region.cover.X ∧
          S.neckCarrierUnion ⊆ S.source_region.carrier ∧
          ∀ x ∈ S.neckCarrierUnion,
            8 * (max C 2) ^ 2 * E.flow.scalar ⟨E.time, E.basepoint⟩ ≤
                E.flow.scalar ⟨E.time, x⟩ ∧
              E.flow.scalar ⟨E.time, x⟩ ≤ 2 * E.flow.scalar ⟨E.time, S.path S.upper⟩ := by
  obtain ⟨epsilon₀, hpos, hthreshold, hratio⟩ :=
    tube.exists_cylinder_scalar_ratio_accuracy.{u}
  refine ⟨epsilon₀, hpos, hthreshold, ?_⟩
  intro epsilon C A D₀ D E S hQ hsmall
  let Q := E.flow.scalar ⟨E.time, E.basepoint⟩
  have hB : 2 ≤ max C 2 := le_max_right C 2
  have hBQ : 0 < (max C 2) ^ 2 * Q :=
    mul_pos (sq_pos_of_pos (lt_of_lt_of_le (by norm_num) hB)) hQ
  have hbounds (N : EpsilonNeck (E.flow.metric E.time)) (hN : N ∈ S.cover.necks)
      (x : (E.flow.slice E.time).carrier) (hx : x ∈ N.carrier) :
      8 * (max C 2) ^ 2 * Q ≤ E.flow.scalar ⟨E.time, x⟩ ∧
        E.flow.scalar ⟨E.time, x⟩ ≤ 2 * E.flow.scalar ⟨E.time, S.path S.upper⟩ := by
    have hcenter := S.center_mem_cover N hN
    rw [S.cover_set] at hcenter
    obtain ⟨v, hv, hcenter⟩ := hcenter
    have hband := S.scalar_band v hv
    have heps : N.epsilon ≤ epsilon₀ := by
      rw [S.cover.neck_epsilon N hN, S.cover_epsilon]
      exact hsmall
    have hcN := N.central_sphere_subset N.center_on_central_sphere
    have hlo := hratio (E.flow.slice E.time).carrier (E.flow.metric E.time)
      (E.flow.connection E.time) N heps N.center hcN x hx
    have hhi := hratio (E.flow.slice E.time).carrier (E.flow.metric E.time)
      (E.flow.connection E.time) N heps x hx N.center hcN
    change E.flow.scalar ⟨E.time, N.center⟩ ≤ 2 * E.flow.scalar ⟨E.time, x⟩ at hlo
    change E.flow.scalar ⟨E.time, x⟩ ≤ 2 * E.flow.scalar ⟨E.time, N.center⟩ at hhi
    rw [← hcenter] at hlo hhi
    constructor <;> nlinarith only [hlo, hhi, hband.1, hband.2]
  have hsubset : S.neckCarrierUnion ⊆ S.source_region.cover.X := by
    rintro x ⟨N, hN, hx⟩
    have hsuper : N.carrier ⊆ {p | 4 * Q < E.flow.scalar ⟨E.time, p⟩} := by
      intro p hp
      have hlo := (hbounds N hN p hp).1
      change 4 * Q < E.flow.scalar ⟨E.time, p⟩
      have hsq : 1 ≤ (max C 2) ^ 2 := by nlinarith only [hB]
      have hcomp := mul_le_mul_of_nonneg_right hsq hQ.le
      nlinarith only [hlo, hcomp, hQ]
    have hcN := N.central_sphere_subset N.center_on_central_sphere
    have hcontain := N.isPreconnected_carrier.subset_connectedComponentIn hcN hsuper
    have hcomp := connectedComponentIn_eq
      (S.source_region.cover_set ▸ S.cover_subset_component (S.center_mem_cover N hN))
    rw [← hcomp, ← S.source_region.cover_set] at hcontain
    exact hcontain hx
  refine ⟨hsubset, hsubset.trans S.source_region.cover_subset, ?_⟩
  rintro x ⟨N, hN, hx⟩
  exact hbounds N hN x hx




theorem exists_source_neck_endpoint_exclusion_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ {epsilon C A D₀ D : ℝ} (E : SameTimeCounterexample.{u} epsilon C A D₀ D)
        (S : CounterexampleNeckSegment E),
        0 < E.flow.scalar ⟨E.time, E.basepoint⟩ → epsilon ≤ epsilon₀ →
        S.path 0 ∉ S.neckCarrierUnion ∧ S.path 1 ∉ S.neckCarrierUnion := by
  obtain ⟨epsilon₀, hpos, hthreshold, hregion⟩ := exists_source_neck_region_accuracy.{u}
  refine ⟨epsilon₀, hpos, hthreshold, ?_⟩
  intro epsilon C A D₀ D E S hQ hsmall
  have hbounds := (hregion E S hQ hsmall).2.2
  let Q := E.flow.scalar ⟨E.time, E.basepoint⟩
  let B := max C 2
  have hB : 2 ≤ B := le_max_right C 2
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hBQ : 0 < B * Q := mul_pos hBpos hQ
  constructor
  · intro hmem
    have hlo := (hbounds (S.path 0) hmem).1
    have hstart := S.source_region.lower_scalar
    have hBmul := mul_le_mul_of_nonneg_right hB hBQ.le
    nlinarith only [hlo, hstart, hBmul, hBQ]
  · intro hmem
    have hhi := (hbounds (S.path 1) hmem).2
    rw [S.upper_scalar_eq] at hhi
    have hendpos : 0 < E.flow.scalar ⟨E.time, S.path 1⟩ :=
      lt_trans (by positivity) S.source_region.upper_scalar
    have hdenom : 0 < 2 * B := by positivity
    have hcut : (E.flow.scalar ⟨E.time, S.path 1⟩ / (2 * B)) * (2 * B) =
        E.flow.scalar ⟨E.time, S.path 1⟩ := div_mul_cancel₀ _ hdenom.ne'
    have hmul := mul_le_mul_of_nonneg_right hhi hdenom.le
    have hBmul := mul_le_mul_of_nonneg_right hB hendpos.le
    nlinarith only [hcut, hmul, hBmul, hendpos]

end PoincareConjecture.M28
