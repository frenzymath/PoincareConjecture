import Mathlib.Topology.Connected.LocallyConnected









set_option autoImplicit false
open Set

namespace Topology

variable {X : Type*} [TopologicalSpace X]



theorem componentIn_closed_two_port_attachment {P D : Set X}
    [LocallyConnectedSpace P] (hP : IsClosed P) (hD : IsClosed D)
    (hDc : IsConnected D) {a b : X} (ha : a ∈ P ∩ D) (hb : b ∈ P ∩ D)
    (hattach : P ∩ D ⊆ connectedComponentIn P a ∪ connectedComponentIn P b) :
    connectedComponentIn (P ∪ D) a =
      (connectedComponentIn P a ∪ connectedComponentIn P b) ∪ D := by
  classical
  let A := connectedComponentIn P a ∪ connectedComponentIn P b
  have hAclosed : IsClosed A := by
    dsimp only [A]
    rw [connectedComponentIn_eq_image ha.1, connectedComponentIn_eq_image hb.1]
    exact (hP.isClosedMap_subtype_val _ isClosed_connectedComponent).union
      (hP.isClosedMap_subtype_val _ isClosed_connectedComponent)
  have hBclosed : IsClosed (P \ A) := by
    have hsub : (Subtype.val : P → X) ''
        (connectedComponent (⟨a, ha.1⟩ : P) ∪
          connectedComponent (⟨b, hb.1⟩ : P))ᶜ = P \ A := by
      rw [image_compl_eq_range_sdiff_image Subtype.val_injective,
        Subtype.range_val, image_union, ← connectedComponentIn_eq_image ha.1,
        ← connectedComponentIn_eq_image hb.1]
    rw [← hsub]
    exact hP.isClosedMap_subtype_val _
      ((isOpen_connectedComponent.union isOpen_connectedComponent).isClosed_compl)
  have hcover : P ∪ D ⊆ (A ∪ D) ∪ (P \ A) := by
    intro x hx
    rcases hx with hx | hx
    · by_cases hxA : x ∈ A
      · exact Or.inl (Or.inl hxA)
      · exact Or.inr ⟨hx, hxA⟩
    · exact Or.inl (Or.inr hx)
  have hsep : Disjoint (A ∪ D) (P \ A) := by
    apply disjoint_left.mpr
    rintro x (hxA | hxD) hx
    · exact hx.2 hxA
    · exact hx.2 (hattach ⟨hx.1, hxD⟩)
  have hupper : connectedComponentIn (P ∪ D) a ⊆ A ∪ D := by
    have h := isPreconnected_iff_subset_of_disjoint_closed.mp
      (isPreconnected_connectedComponentIn (F := P ∪ D) (x := a))
      (A ∪ D) (P \ A) (hAclosed.union hD) hBclosed
      ((connectedComponentIn_subset (P ∪ D) a).trans hcover)
      (by rw [hsep.inter_eq, inter_empty])
    rcases h with h | h
    · exact h
    · exact False.elim ((h (mem_connectedComponentIn (Or.inl ha.1))).2
        (Or.inl (mem_connectedComponentIn ha.1)))
  have hDa : D ⊆ connectedComponentIn (P ∪ D) a :=
    hDc.isPreconnected.subset_connectedComponentIn ha.2 subset_union_right
  have hba : b ∈ connectedComponentIn (P ∪ D) a := hDa hb.2
  apply Subset.antisymm hupper
  apply union_subset _ hDa
  apply union_subset (connectedComponentIn_mono a subset_union_left)
  have hB := connectedComponentIn_mono b (show P ⊆ P ∪ D from subset_union_left)
  rwa [connectedComponentIn_eq hba] at *


theorem componentIn_closed_two_port_attachment_eq_of_not_mem {P D : Set X}
    [LocallyConnectedSpace P] (hP : IsClosed P) (hD : IsClosed D)
    (hDc : IsConnected D) {a b x : X} (ha : a ∈ P ∩ D) (hb : b ∈ P ∩ D)
    (hattach : P ∩ D ⊆ connectedComponentIn P a ∪ connectedComponentIn P b)
    (hx : x ∈ P)
    (hxports : x ∉ connectedComponentIn P a ∪ connectedComponentIn P b) :
    connectedComponentIn (P ∪ D) x = connectedComponentIn P x := by
  have heq := componentIn_closed_two_port_attachment hP hD hDc ha hb hattach
  have hnot : x ∉ connectedComponentIn (P ∪ D) a := by
    rw [heq]
    rintro (hxA | hxD)
    · exact hxports hxA
    · exact hxports (hattach ⟨hx, hxD⟩)
  have hsub : connectedComponentIn (P ∪ D) x ⊆ P := by
    intro y hy
    rcases connectedComponentIn_subset (P ∪ D) x hy with hyP | hyD
    · exact hyP
    · have hya : y ∈ connectedComponentIn (P ∪ D) a := heq.symm ▸ Or.inr hyD
      have hsame := (connectedComponentIn_eq hy).trans (connectedComponentIn_eq hya).symm
      exact False.elim (hnot (hsame ▸ mem_connectedComponentIn (Or.inl hx)))
  exact Subset.antisymm
    (isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn (Or.inl hx)) hsub)
    (connectedComponentIn_mono x subset_union_left)



theorem componentIn_closed_attachment_of_two_connected_ports {P D p q : Set X}
    [LocallyConnectedSpace P] (hP : IsClosed P) (hD : IsClosed D)
    (hDc : IsConnected D) (hp : IsConnected p) (hq : IsConnected q)
    (hports : P ∩ D = p ∪ q) {a b : X} (ha : a ∈ p) (hb : b ∈ q) :
    connectedComponentIn (P ∪ D) a =
        (connectedComponentIn P a ∪ connectedComponentIn P b) ∪ D ∧
      ∀ x ∈ P, x ∉ connectedComponentIn P a ∪ connectedComponentIn P b →
        connectedComponentIn (P ∪ D) x = connectedComponentIn P x := by
  have hpP : p ⊆ P := subset_union_left.trans (hports.symm.subset.trans inter_subset_left)
  have hqP : q ⊆ P := subset_union_right.trans (hports.symm.subset.trans inter_subset_left)
  have ha' : a ∈ P ∩ D := hports.symm ▸ Or.inl ha
  have hb' : b ∈ P ∩ D := hports.symm ▸ Or.inr hb
  have hattach : P ∩ D ⊆ connectedComponentIn P a ∪ connectedComponentIn P b := by
    rw [hports]
    exact union_subset_union (hp.isPreconnected.subset_connectedComponentIn ha hpP)
      (hq.isPreconnected.subset_connectedComponentIn hb hqP)
  exact ⟨componentIn_closed_two_port_attachment hP hD hDc ha' hb' hattach,
    fun _ hx hmiss => componentIn_closed_two_port_attachment_eq_of_not_mem
      hP hD hDc ha' hb' hattach hx hmiss⟩

end Topology
