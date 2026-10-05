import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonRegionRecognition

/-!
# Exact region labels for two local complementary sides

At a boundary point of a regular closed region, every open
neighborhood meets both its interior and its exterior. Two
preconnected local sides avoiding the boundary consequently
have opposite labels. Their full closures give exact closed
region intersections. See Erickson, Simple Polygons, pp. 2--4,
Alexander 1924, pp. 6--8 and M76 derivation 283.
-/

set_option autoImplicit false

open Set

namespace IsClosed

variable {X : Type*} [TopologicalSpace X]

/-- Two preconnected sides in an open neighborhood of a
regular closed region's boundary point lie on opposite sides
of that region. Empty sides are allowed in the premises;
the boundary witnesses force both to be nonempty.
See Alexander pp. 6--8 and M76 derivation 283. -/
theorem local_complementary_sides {D U L R : Set X} (hD : IsClosed D)
    (hreg : closure (interior D) = D) {p : X} (hp : p ∈ frontier D)
    (hU : IsOpen U) (hpU : p ∈ U)
    (hL : IsPreconnected L) (hR : IsPreconnected R)
    (hcover : U \ frontier D = L ∪ R) :
    (L ⊆ interior D ∧ R ⊆ Dᶜ) ∨ (R ⊆ interior D ∧ L ⊆ Dᶜ) := by
  have hLR : L ∪ R ⊆ (frontier D)ᶜ := by
    rw [← hcover]
    exact fun _ hx => hx.2
  have hside_in {T : Set X} (hT : IsPreconnected T)
      (hTfront : T ⊆ (frontier D)ᶜ) (hmeet : (T ∩ interior D).Nonempty) :
      T ⊆ interior D := by
    apply hT.m76_subset_of_disjoint_frontier isOpen_interior ?_ hmeet
    exact Set.disjoint_left.mpr
      (fun _ hx hy => hTfront hy (frontier_interior_subset hx))
  have hside_out {T : Set X} (hT : IsPreconnected T)
      (hTfront : T ⊆ (frontier D)ᶜ) (hmeet : (T ∩ Dᶜ).Nonempty) : T ⊆ Dᶜ := by
    apply hT.m76_subset_of_disjoint_frontier hD.isOpen_compl ?_ hmeet
    rw [frontier_compl]
    exact Set.disjoint_left.mpr (fun _ hx hy => hTfront hy hx)
  have hpD : p ∈ D := hD.closure_eq ▸ hp.1
  have hpI : p ∈ closure (interior D) := hreg.symm ▸ hpD
  have hpO : p ∈ closure Dᶜ := by
    rw [closure_compl]
    exact hp.2
  obtain ⟨x, hxU, hxI⟩ := mem_closure_iff.mp hpI U hU hpU
  obtain ⟨y, hyU, hyO⟩ := mem_closure_iff.mp hpO U hU hpU
  have hxLR : x ∈ L ∪ R := hcover.subset ⟨hxU, fun h => h.2 hxI⟩
  have hyLR : y ∈ L ∪ R :=
    hcover.subset ⟨hyU, fun h => hyO (hD.closure_eq ▸ h.1)⟩
  rcases hxLR with hxL | hxR
  · have hLI := hside_in hL (subset_union_left.trans hLR) ⟨x, hxL, hxI⟩
    have hyR : y ∈ R := hyLR.resolve_left
      (fun hyL => hyO (interior_subset (hLI hyL)))
    exact Or.inl ⟨hLI, hside_out hR (subset_union_right.trans hLR) ⟨y, hyR, hyO⟩⟩
  · have hRI := hside_in hR (subset_union_right.trans hLR) ⟨x, hxR, hxI⟩
    have hyL : y ∈ L := hyLR.resolve_right
      (fun hyR => hyO (interior_subset (hRI hyR)))
    exact Or.inr ⟨hRI, hside_out hL (subset_union_left.trans hLR) ⟨y, hyL, hyO⟩⟩

/-- Once the two open sides have opposite region labels,
their full closures have an exact intersection with the
closed region. The outside closure may meet the region only
along boundary points already in the inside closure.
See Alexander pp. 6--8 and M76 derivation 283. -/
theorem inter_union_closure_eq_of_sides {D L R : Set X} (hD : IsClosed D)
    (hL : L ⊆ interior D) (hR : R ⊆ Dᶜ)
    (hrim : closure R ∩ frontier D ⊆ closure L) :
    D ∩ (closure L ∪ closure R) = closure L := by
  have hclL : closure L ⊆ D := closure_minimal (hL.trans interior_subset) hD
  have hclR : closure R ⊆ (interior D)ᶜ := by
    simpa only [closure_compl] using closure_mono hR
  apply Subset.antisymm
  · rintro x ⟨hxD, hxL | hxR⟩
    · exact hxL
    · exact hrim ⟨hxR, subset_closure hxD, hclR hxR⟩
  · intro x hx
    exact ⟨hclL hx, Or.inl hx⟩

end IsClosed
