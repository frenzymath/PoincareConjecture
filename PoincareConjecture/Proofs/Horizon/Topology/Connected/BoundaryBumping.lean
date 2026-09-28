import Mathlib.Topology.Separation.Regular



noncomputable section
set_option autoImplicit false

open Set

namespace Poincare.Topology



theorem connectedComponentIn_inter_frontier_nonempty
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [PreconnectedSpace X] {K : Set X} (hK : IsClosed K) (hproper : K ≠ univ)
    {x : X} (hx : x ∈ K) :
    (connectedComponentIn K x ∩ frontier K).Nonempty := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  let z : K := ⟨x, hx⟩
  let B : Set K := Subtype.val ⁻¹' frontier K
  have hB : IsCompact B := (isClosed_frontier.preimage continuous_subtype_val).isCompact
  by_contra hnone
  have hdisj : B ∩ connectedComponent z = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro y ⟨hyB, hyC⟩
    apply hnone
    refine ⟨y, ?_, hyB⟩
    rw [connectedComponentIn_eq_image hx]
    exact ⟨y, hyC, rfl⟩
  rw [connectedComponent_eq_iInter_isClopen] at hdisj
  obtain ⟨s, hs⟩ := hB.elim_finite_subfamily_closed
    (fun V : {V : Set K // IsClopen V ∧ z ∈ V} => (V : Set K))
    (fun V => V.property.1.isClosed) hdisj
  let V : Set K := ⋂ i ∈ s, (i : Set K)
  have hV : IsClopen V := isClopen_biInter_finset fun i _ => i.property.1
  have hzV : z ∈ V := mem_iInter₂.mpr fun i _ => i.property.2
  have hVint : Subtype.val '' V ⊆ interior K := by
    rintro y ⟨w, hw, rfl⟩
    by_contra hwint
    have hwB : w ∈ B := by
      change (w : X) ∈ frontier K
      rw [hK.frontier_eq]
      exact ⟨w.property, hwint⟩
    exact (show (B ∩ V).Nonempty from ⟨w, hwB, hw⟩).ne_empty hs
  have hclosed : IsClosed (Subtype.val '' V : Set X) :=
    hK.isClosedEmbedding_subtypeVal.isClosedMap V hV.isClosed
  obtain ⟨O, hO, hOV⟩ := isOpen_induced_iff.mp hV.isOpen
  have heq : Subtype.val '' V = O ∩ interior K := by
    ext y
    constructor
    · intro hy
      have hyint := hVint hy
      rcases hy with ⟨w, hw, rfl⟩
      rw [← hOV] at hw
      exact ⟨hw, hyint⟩
    · rintro ⟨hyO, hyK⟩
      refine ⟨⟨y, interior_subset hyK⟩, ?_, rfl⟩
      rw [← hOV]
      exact hyO
  have hopen : IsOpen (Subtype.val '' V : Set X) := heq ▸ hO.inter isOpen_interior
  have hall : (Subtype.val '' V : Set X) = univ :=
    (show IsClopen (Subtype.val '' V : Set X) from ⟨hclosed, hopen⟩).eq_univ
      ⟨x, z, hzV, rfl⟩
  apply hproper
  apply eq_univ_of_univ_subset
  rw [← hall]
  exact hVint.trans interior_subset



theorem connectedComponentIn_diff_inter_frontier_nonempty
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {C V : Set X} (hC : IsCompact C) (hconn : IsConnected C)
    (hV : IsOpen V) (hmeet : (C ∩ V).Nonempty) {x : X} (hx : x ∈ C \ V) :
    (connectedComponentIn (C \ V) x ∩ frontier V).Nonempty := by
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.mp hconn.isPreconnected
  let K : Set C := Subtype.val ⁻¹' Vᶜ
  have hK : IsClosed K := hV.isClosed_compl.preimage continuous_subtype_val
  have hproper : K ≠ univ := by
    intro hall
    obtain ⟨y, hyC, hyV⟩ := hmeet
    have hmem : (⟨y, hyC⟩ : C) ∈ K := hall ▸ mem_univ _
    exact hmem hyV
  obtain ⟨y, hy, hyfront⟩ := connectedComponentIn_inter_frontier_nonempty
    hK hproper (show (⟨x, hx.1⟩ : C) ∈ K from hx.2)
  refine ⟨y, ?_, ?_⟩
  · have hsub : Subtype.val '' connectedComponentIn K (⟨x, hx.1⟩ : C) ⊆ C \ V := by
      rintro z ⟨w, hw, rfl⟩
      exact ⟨w.property, connectedComponentIn_subset K _ hw⟩
    exact ((isPreconnected_connectedComponentIn.image Subtype.val
      continuous_subtype_val.continuousOn).subset_connectedComponentIn
        ⟨⟨x, hx.1⟩, mem_connectedComponentIn hx.2, rfl⟩ hsub) ⟨y, hy, rfl⟩
  · have hh := continuous_subtype_val.frontier_preimage_subset Vᶜ hyfront
    rwa [frontier_compl] at hh

end Poincare.Topology
