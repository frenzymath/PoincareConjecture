import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.RelativeEndpointChart

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.HamiltonIntervalTorus

theorem relative_preimage_frontier_subset
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    {R : Set X} (hR : IsCompact R) (q : C(R, Y)) {A : Set Y} (hA : IsClosed A) :
    frontier (Subtype.val '' (q ⁻¹' A)) ⊆
      (Subtype.val '' (q ⁻¹' A)) ∩ frontier R ∪
        Subtype.val '' (q ⁻¹' frontier A) := by
  let : CompactSpace R := isCompact_iff_compactSpace.mp hR
  have hN : IsCompact (Subtype.val '' (q ⁻¹' A)) :=
    (hA.preimage q.continuous).isCompact.image continuous_subtype_val
  intro x hx
  have hxN := hN.isClosed.frontier_subset hx
  by_cases hxB : x ∈ frontier R
  · exact Or.inl ⟨hxN, hxB⟩
  · obtain ⟨y, hyA, rfl⟩ := hxN
    by_cases hyB : q y ∈ frontier A
    · exact Or.inr ⟨y, hyB, rfl⟩
    · have hyR : (y : X) ∈ interior R :=
        (mem_interior_iff_notMem_frontier y.property).mpr hxB
      have hyI : q y ∈ interior A :=
        (mem_interior_iff_notMem_frontier (show q y ∈ A from hyA)).mpr hyB
      obtain ⟨U, hU, hUq⟩ := isOpen_induced_iff.mp
        (isOpen_interior.preimage q.continuous)
      have hyU : (y : X) ∈ U := hUq.symm.subset hyI
      have hsub : interior R ∩ U ⊆ Subtype.val '' (q ⁻¹' A) := by
        intro z hz
        have hzq : q ⟨z, interior_subset hz.1⟩ ∈ interior A := hUq.subset hz.2
        exact ⟨⟨z, interior_subset hz.1⟩,
          show q ⟨z, interior_subset hz.1⟩ ∈ A from interior_subset hzq, rfl⟩
      have hyN : (y : X) ∈ interior (Subtype.val '' (q ⁻¹' A)) :=
        (interior_maximal hsub (isOpen_interior.inter hU)) ⟨hyR, hyU⟩
      exact False.elim (disjoint_left.mp disjoint_interior_frontier hyN hx)

end PoincareConjecture.M76.HamiltonIntervalTorus
