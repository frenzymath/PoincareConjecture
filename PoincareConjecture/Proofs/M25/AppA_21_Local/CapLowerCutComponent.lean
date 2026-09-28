import PoincareConjecture.Proofs.M25.AppA_21_Local.CapEndSeparation
import PoincareConjecture.Proofs.M25.AppA_1_Necks.RetainedLevelComponents
import Mathlib.Topology.Connected.LocallyConnected

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem CapCertificate.end_neck_lower_cut_eq_negative_component
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C : CapCertificate g) {t : ℝ}
    (ht : t ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹) :
    let L := C.epsilon⁻¹
    let N := C.end_neck
    let q := (N.coordinate_inverse N.center).1
    let S := range (fun v : UnitTwoSphere => N.coordinate_map (v, t))
    let A := connectedComponentIn Sᶜ
      (N.coordinate_map (q, (t - L) / 2))
    C.closed_core ∪ N.region (-L) t = A ∧
      C.carrier \ N.region t L = closure A ∧
      IsCompact (closure A) ∧ frontier A = S := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let L := C.epsilon⁻¹
  let N := C.end_neck
  let q := (N.coordinate_inverse N.center).1
  let S := range (fun v : UnitTwoSphere => N.coordinate_map (v, t))
  let A := connectedComponentIn Sᶜ (N.coordinate_map (q, (t - L) / 2))
  let U := C.closed_core ∪ N.region (-L) t
  let K := C.carrier \ N.region t L
  change U = A ∧ K = closure A ∧ IsCompact (closure A) ∧ frontier A = S
  have hN : N.epsilon = C.epsilon := C.end_neck_epsilon
  have hL : 0 < L := inv_pos.mpr C.epsilon_pos
  have htN : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    simpa only [hN] using ht
  have hST : N.coordinate_map '' (univ ×ˢ ({t} : Set ℝ)) = S := by
    apply Subset.antisymm
    · rintro x ⟨⟨v, s⟩, ⟨_, hs⟩, rfl⟩
      have hst : s = t := hs
      subst s
      exact ⟨v, rfl⟩
    · rintro x ⟨v, rfl⟩
      exact ⟨(v, t), ⟨mem_univ _, rfl⟩, rfl⟩
  obtain ⟨_, hUopen, hUclosure, _, hUfront0, _, _⟩ :=
    C.end_neck_lower_cut_topology ht
  have hUfront : frontier U = S := hUfront0.trans hST
  have hSclosed : IsClosed S := by rw [← hUfront]; exact isClosed_frontier
  have hUavoid : Disjoint U S := by
    apply disjoint_left.mpr
    intro x hxU hxS
    rw [← hUfront, hUopen.frontier_eq] at hxS
    exact hxS.2 hxU
  have hUsub : U ⊆ C.carrier := by
    intro x hx
    rcases hx with hxcore | hxN
    · rw [C.closed_core_eq_complement_end] at hxcore
      exact hxcore.1
    · exact C.end_neck_subset hxN.1
  have hcover : C.carrier ⊆ U ∪ N.carrier := by
    intro x hx
    by_cases hxN : x ∈ N.carrier
    · exact Or.inr hxN
    · apply Or.inl
      apply Or.inl
      rw [C.closed_core_eq_complement_end]
      exact ⟨hx, hxN⟩
  have hUN : U ∩ N.carrier ⊆ N.region (-L) t := by
    intro x hx
    rcases hx.1 with hxcore | hxnegative
    · rw [C.closed_core_eq_complement_end] at hxcore
      exact (hxcore.2 hx.2).elim
    · exact hxnegative
  have hpointDom : (t - L) / 2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    rw [hN]
    change -L < (t - L) / 2 ∧ (t - L) / 2 < L
    change -L < t ∧ t < L at ht
    constructor <;> linarith only [ht.1, ht.2, hL]
  have hpoint : N.coordinate_map (q, (t - L) / 2) ∈ N.region (-L) t := by
    refine ⟨N.coordinate_map_mem ⟨mem_univ _, hpointDom⟩, ?_⟩
    rw [N.coordinate_inverse_map (q, (t - L) / 2) hpointDom]
    change -L < (t - L) / 2 ∧ (t - L) / 2 < t
    change -L < t ∧ t < L at ht
    constructor <;> linarith only [ht.1, ht.2, hL]
  obtain ⟨a, b, _, _, hnegative0, _, _, hfront0, _, _⟩ :=
    N.exists_opposite_retained_components C.end_neck_isSeparating htN
  have hnegative1 : N.region (-L) t ⊆ connectedComponentIn Sᶜ a := by
    simpa only [hN] using hnegative0
  have hcanonical : connectedComponentIn Sᶜ a = A :=
    connectedComponentIn_eq (hnegative1 hpoint)
  have hnegative : N.region (-L) t ⊆ A := by
    rw [← hcanonical]
    exact hnegative1
  have hfront : frontier A = S := by
    rw [← hcanonical]
    exact hfront0
  have hAopen : IsOpen A := hSclosed.isOpen_compl.connectedComponentIn
  have hApre : IsPreconnected A := isPreconnected_connectedComponentIn
  have hAsub : A ⊆ Sᶜ := connectedComponentIn_subset _ _
  have hAU : A ⊆ U := by
    apply hApre.subset_of_closure_inter_subset hUopen
      ⟨N.coordinate_map (q, (t - L) / 2), hnegative hpoint, Or.inr hpoint⟩
    intro x hx
    by_contra hxU
    have hxfront : x ∈ frontier U := by
      rw [hUopen.frontier_eq]
      exact ⟨hx.1, hxU⟩
    exact hAsub hx.2 (hUfront ▸ hxfront)
  let P := A ∪ N.carrier
  let Q := U ∩ (closure A)ᶜ
  have hPopen : IsOpen P := hAopen.union N.carrier_open
  have hQopen : IsOpen Q := hUopen.inter isClosed_closure.isOpen_compl
  have hPQcover : C.carrier ⊆ P ∪ Q := by
    intro x hx
    rcases hcover hx with hxU | hxN
    · by_cases hxA : x ∈ A
      · exact Or.inl (Or.inl hxA)
      · apply Or.inr
        refine ⟨hxU, ?_⟩
        intro hxclosure
        rw [closure_eq_self_union_frontier, hfront] at hxclosure
        rcases hxclosure with hxA' | hxS
        · exact hxA hxA'
        · exact disjoint_left.mp hUavoid hxU hxS
    · exact Or.inl (Or.inr hxN)
  have hPQdisjoint : Disjoint P Q := by
    apply disjoint_left.mpr
    intro x hxP hxQ
    rcases hxP with hxA | hxN
    · exact hxQ.2 (subset_closure hxA)
    · exact hxQ.2 (subset_closure (hnegative (hUN ⟨hxQ.1, hxN⟩)))
  have hCP : C.carrier ⊆ P := by
    rcases C.m25_isConnected_carrier.isPreconnected.subset_or_subset
      hPopen hQopen hPQdisjoint hPQcover with hCP | hCQ
    · exact hCP
    · have hcN : N.center ∈ N.carrier :=
        N.central_sphere_subset N.center_on_central_sphere
      exact (disjoint_left.mp hPQdisjoint (Or.inr hcN)
        (hCQ (C.end_neck_subset hcN))).elim
  have hUA : U ⊆ A := by
    intro x hx
    rcases hCP (hUsub hx) with hxA | hxN
    · exact hxA
    · exact hnegative (hUN ⟨hx, hxN⟩)
  have heq : U = A := Subset.antisymm hUA hAU
  have hK : K = closure A := by
    rw [← heq]
    exact hUclosure.symm
  refine ⟨heq, hK, ?_, hfront⟩
  rw [← hK]
  exact C.isCompact_end_neck_lower_cut ht

end PoincareConjecture
