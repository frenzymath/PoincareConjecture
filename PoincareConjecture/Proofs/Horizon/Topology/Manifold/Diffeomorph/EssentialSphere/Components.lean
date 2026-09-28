import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.Connected

set_option autoImplicit false

open Set Topology

namespace Poincare.Topology

variable {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]

theorem isConnected_inter_of_frontier_subset
    {U A V : Set X} (hU : IsOpen U) (hcU : IsConnected U)
    (hA : IsOpen A) (hV : IsOpen V) (hVU : V ⊆ U)
    (hc : IsConnected (A ∩ V)) (hfront : frontier A ∩ U ⊆ V)
    (hne : (U \ A).Nonempty) : IsConnected (U ∩ A) := by
  let : ConnectedSpace U := isConnected_iff_connectedSpace.mp hcU
  let : LocallyConnectedSpace U := hU.locallyConnectedSpace
  have hc' : IsConnected ((Subtype.val : U → X) ⁻¹' A ∩
      (Subtype.val : U → X) ⁻¹' V) :=
    hc.preimage_of_isOpenMap Subtype.val_injective hU.isOpenMap_subtype_val
      (by rintro x ⟨_, hx⟩; exact ⟨⟨x, hVU hx⟩, rfl⟩)
  have hfront' : frontier ((Subtype.val : U → X) ⁻¹' A) ⊆
      (Subtype.val : U → X) ⁻¹' V := by
    intro x hx
    exact hfront ⟨continuous_subtype_val.frontier_preimage_subset A hx, x.property⟩
  have hne' : (Subtype.val : U → X) ⁻¹' A ≠ univ := by
    intro h
    obtain ⟨x, hxU, hxA⟩ := hne
    exact hxA (show (⟨x, hxU⟩ : U) ∈ (Subtype.val : U → X) ⁻¹' A from
      h.symm ▸ mem_univ _)
  have h := isConnected_of_inter_of_frontier_subset
    (hA.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
    hc' hfront' hne'
  have heq : (Subtype.val : U → X) '' ((Subtype.val : U → X) ⁻¹' A) = U ∩ A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hxU, hxA⟩
      exact ⟨⟨x, hxU⟩, hxA, rfl⟩
  rw [← heq]
  exact h.image _ continuous_subtype_val.continuousOn

theorem connected_components_of_closed_cut
    {U K V : Set X} (hU : IsOpen U) (hcU : IsConnected U)
    (hK : IsClosed K) (hV : IsOpen V) (hVU : V ⊆ U)
    (hfront : frontier K ⊆ V)
    (hleft : IsConnected (interior K ∩ V))
    (hright : IsConnected (Kᶜ ∩ V)) :
    IsConnected (U ∩ interior K) ∧ IsConnected (U \ K) ∧
      (U ∩ interior K) ∪ (U \ K) = U \ frontier K ∧
      (∀ x ∈ U ∩ interior K,
        connectedComponentIn (U \ frontier K) x = U ∩ interior K) ∧
      ∀ x ∈ U \ K, connectedComponentIn (U \ frontier K) x = U \ K := by
  have hL : IsConnected (U ∩ interior K) := by
    apply isConnected_inter_of_frontier_subset hU hcU isOpen_interior hV hVU hleft
    · exact fun x hx => hfront (frontier_interior_subset hx.1)
    · obtain ⟨x, hxK, hxV⟩ := hright.nonempty
      exact ⟨x, hVU hxV, fun hx => hxK (interior_subset hx)⟩
  have hR : IsConnected (U \ K) := by
    apply isConnected_inter_of_frontier_subset hU hcU hK.isOpen_compl hV hVU hright
    · simpa only [frontier_compl] using
        (inter_subset_left.trans hfront : frontier K ∩ U ⊆ V)
    · obtain ⟨x, hxK, hxV⟩ := hleft.nonempty
      exact ⟨x, hVU hxV, fun hx => hx (interior_subset hxK)⟩
  have hcover : (U ∩ interior K) ∪ (U \ K) = U \ frontier K := by
    rw [hK.frontier_eq]
    ext x
    simp only [mem_union, mem_inter_iff, mem_sdiff]
    tauto
  have hdis : Disjoint (U ∩ interior K) (U \ K) :=
    disjoint_left.mpr fun _ hx hy => hy.2 (interior_subset hx.2)
  refine ⟨hL, hR, hcover, ?_, ?_⟩
  · intro x hx
    rw [← hcover]
    exact connectedComponentIn_eq_of_open_partition (hU.inter isOpen_interior)
      (hU.inter hK.isOpen_compl) hdis hL.isPreconnected hx
  · intro x hx
    rw [← hcover, union_comm]
    exact connectedComponentIn_eq_of_open_partition (hU.inter hK.isOpen_compl)
      (hU.inter isOpen_interior) hdis.symm hR.isPreconnected hx

end Poincare.Topology
