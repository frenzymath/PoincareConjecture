import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.ClosedConnectedAttachment

set_option autoImplicit false
open Set

namespace Topology

variable {X : Type*} [TopologicalSpace X]

theorem mem_componentIn_iff_component_class {P : Set X} {x y : X}
    (hx : x ∈ P) (hy : y ∈ P) :
    y ∈ connectedComponentIn P x ↔
      ConnectedComponents.mk (⟨y, hy⟩ : P) = ConnectedComponents.mk (⟨x, hx⟩ : P) := by
  rw [connectedComponentIn_eq_image hx, ConnectedComponents.coe_eq_coe']
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hz' : z = (⟨y, hy⟩ : P) := Subtype.ext hzy
    exact hz' ▸ hz
  · intro hyc
    exact ⟨⟨y, hy⟩, hyc, rfl⟩

theorem mem_componentIn_closed_attachment_iff {P D : Set X}
    (hP : IsClosed P) (hD : IsClosed D) (hDc : IsConnected D)
    (hPD : IsConnected (P ∩ D)) {x y : X} (hx : x ∈ P) (hy : y ∈ P) :
    y ∈ connectedComponentIn (P ∪ D) x ↔ y ∈ connectedComponentIn P x := by
  obtain ⟨H, hH⟩ := exists_components_homeomorph_closed_attachment hP hD hDc hPD
  rw [mem_componentIn_iff_component_class (P := P ∪ D) (x := x) (y := y)
      (Or.inl hx) (Or.inl hy),
    mem_componentIn_iff_component_class (P := P) (x := x) (y := y) hx hy,
    ← hH ⟨y, hy⟩, ← hH ⟨x, hx⟩]
  exact H.injective.eq_iff

theorem componentIn_closed_attachment_eq_union {P D : Set X}
    (hP : IsClosed P) (hD : IsClosed D) (hDc : IsConnected D)
    (hPD : IsConnected (P ∩ D)) {b x : X}
    (hb : b ∈ P ∩ D) (hx : x ∈ P) (hbx : b ∈ connectedComponentIn P x) :
    connectedComponentIn (P ∪ D) x = connectedComponentIn P x ∪ D := by
  have hDb : D ⊆ connectedComponentIn (P ∪ D) b :=
    hDc.isPreconnected.subset_connectedComponentIn hb.2 subset_union_right
  have hbnew : b ∈ connectedComponentIn (P ∪ D) x :=
    connectedComponentIn_mono x subset_union_left hbx
  apply Subset.antisymm
  · intro y hy
    rcases connectedComponentIn_subset (P ∪ D) x hy with hyP | hyD
    · exact Or.inl ((mem_componentIn_closed_attachment_iff hP hD hDc hPD hx hyP).mp hy)
    · exact Or.inr hyD
  · apply union_subset
    · exact connectedComponentIn_mono x subset_union_left
    · rwa [connectedComponentIn_eq hbnew]

theorem componentIn_closed_attachment_eq_of_not_mem {P D : Set X}
    (hP : IsClosed P) (hD : IsClosed D) (hDc : IsConnected D)
    (hPD : IsConnected (P ∩ D)) {b x : X}
    (hb : b ∈ P ∩ D) (hx : x ∈ P) (hbx : b ∉ connectedComponentIn P x) :
    connectedComponentIn (P ∪ D) x = connectedComponentIn P x := by
  apply Subset.antisymm
  · intro y hy
    rcases connectedComponentIn_subset (P ∪ D) x hy with hyP | hyD
    · exact (mem_componentIn_closed_attachment_iff hP hD hDc hPD hx hyP).mp hy
    · have hDy : D ⊆ connectedComponentIn (P ∪ D) y :=
        hDc.isPreconnected.subset_connectedComponentIn hyD subset_union_right
      have hbnew : b ∈ connectedComponentIn (P ∪ D) x := by
        rw [connectedComponentIn_eq hy]
        exact hDy hb.2
      exact (hbx ((mem_componentIn_closed_attachment_iff hP hD hDc hPD hx hb.1).mp
        hbnew)).elim
  · exact connectedComponentIn_mono x subset_union_left

end Topology
