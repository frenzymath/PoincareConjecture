import PoincareConjecture.Proofs.M76.Wall.PLDomainComponents











set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)





theorem two_component_frontiers_of_boundary_pieces
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {Q : Set X}
    (hQ : IsCompact Q) (he : PLDomain e Q)
    (a : Bool → X) (ha : ∀ b, a b ∈ Q)
    (C k cap : Bool → Set X)
    (hC : ∀ b, C b = connectedComponentIn Q (a b))
    (hdis : Disjoint (C false) (C true))
    (hk : ∀ b, IsPreconnected (k b))
    (hcap : ∀ b, cap b ⊆ C b)
    (hmeet : ∀ b, (k b ∩ cap b).Nonempty)
    (hboundary : frontier Q =
      (k false ∪ cap false) ∪ (k true ∪ cap true)) :
    ∀ b, IsCompact (C b) ∧ PLDomain e (C b) ∧ IsConnected (C b) ∧
      k b ⊆ C b ∧ frontier (C b) = k b ∪ cap b := by
  let : LocallyPathConnectedSpace Q := he.locallyPathConnectedSpace
  have hsub (b : Bool) : C b ⊆ Q := by
    rw [hC]
    exact connectedComponentIn_subset Q (a b)
  have hcompact (b : Bool) : IsCompact (C b) := by
    rw [hC]
    exact isCompact_connectedComponentIn_of_mem hQ (ha b)
  have hpart (b : Bool) : k b ∪ cap b ⊆ frontier Q := by
    rw [hboundary]
    cases b
    · exact subset_union_left
    · exact subset_union_right
  have hkC (b : Bool) : k b ⊆ C b := by
    obtain ⟨x, hxk, hxcap⟩ := hmeet b
    have hxC : x ∈ connectedComponentIn Q (a b) := (hC b) ▸ hcap b hxcap
    have hwhole := (hk b).subset_connectedComponentIn hxk
      ((subset_union_left.trans (hpart b)).trans hQ.isClosed.frontier_subset)
    rw [hC]
    rw [connectedComponentIn_eq hxC]
    exact hwhole
  have hfront (b : Bool) : frontier (C b) = C b ∩ frontier Q := by
    have hopen : IsOpen ((Subtype.val : Q → X) ⁻¹' C b) := by
      rw [hC]
      exact isOpen_preimage_connectedComponentIn (ha b)
    obtain ⟨U, hU, hCU⟩ := exists_open_inter_of_relative_open (hsub b) hopen
    exact frontier_eq_inter_of_eq_inter_open hQ.isClosed (hcompact b).isClosed hU hCU
  have hpC (b : Bool) : k b ∪ cap b ⊆ C b := union_subset (hkC b) (hcap b)
  have hd (b : Bool) : Disjoint (C b) (k (!b) ∪ cap (!b)) := by
    cases b
    · exact hdis.mono_right (hpC true)
    · exact hdis.symm.mono_right (hpC false)
  intro b
  refine ⟨hcompact b, ?_, ?_, hkC b, ?_⟩
  · rw [hC]
    exact he.connectedComponentIn hQ (ha b)
  · rw [hC]
    exact isConnected_connectedComponentIn_iff.mpr (ha b)
  · rw [hfront, hboundary]
    have hown : C b ∩ (k b ∪ cap b) = k b ∪ cap b :=
      inter_eq_right.mpr (hpC b)
    have hother : C b ∩ (k (!b) ∪ cap (!b)) = ∅ := (hd b).inter_eq
    rw [inter_union_distrib_left]
    cases b
    · change C false ∩ (k true ∪ cap true) = ∅ at hother
      rw [hown, hother, union_empty]
    · change C true ∩ (k false ∪ cap false) = ∅ at hother
      rw [hown, hother, empty_union]



theorem two_component_frontiers_of_marked_rims
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {Q : Set X}
    (hQ : IsCompact Q) (he : PLDomain e Q)
    (a : Bool → X) (ha : ∀ b, a b ∈ Q)
    (C k cap q : Bool → Set X)
    (hC : ∀ b, C b = connectedComponentIn Q (a b))
    (hdis : Disjoint (C false) (C true))
    (hk : ∀ b, IsPreconnected (k b))
    (hcap : ∀ b, cap b ⊆ C b)
    (hrim : ∀ b, k b ∩ cap b = q b) (hq : ∀ b, (q b).Nonempty)
    (hboundary : frontier Q =
      (k false ∪ cap false) ∪ (k true ∪ cap true)) :
    ∀ b, IsCompact (C b) ∧ PLDomain e (C b) ∧ IsConnected (C b) ∧
      k b ⊆ C b ∧ frontier (C b) = k b ∪ cap b :=
  two_component_frontiers_of_boundary_pieces hQ he a ha C k cap hC hdis hk hcap
    (fun b => (hrim b).symm ▸ hq b) hboundary

end PoincareConjecture.M76
