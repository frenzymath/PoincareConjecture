import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Arcs
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Strips.Contacts
import PoincareConjecture.Proofs.Horizon.Topology.Connected.FourContacts.Resolution

noncomputable section
set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SaddleLevel

open Poincare.Topology

private abbrev E2 := EuclideanSpace Real (Fin 2)

variable {M : Type*} [TopologicalSpace M]

private theorem positive_contact_mem (e : OpenPartialHomeomorph E2 M)
    {r t : Real} (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2) (j : Fin 2 × Fin 2) :
    e (movingContact r t j) ∈ positivePatchArc e r t j.2 := by
  rw [movingContact_eq_positive hr ht.le]
  exact positiveContact_mem_patchArc e hr htr _ _

private theorem negative_contact_mem (e : OpenPartialHomeomorph E2 M)
    {r t : Real} (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2) (j : Fin 2 × Fin 2) :
    e (movingContact r (-t) j) ∈ negativePatchArc e r t j.1 := by
  rw [movingContact_eq_negative hr (neg_nonpos.mpr ht.le), neg_neg]
  exact negativeContact_mem_patchArc e hr htr _ _

theorem positive_level_connected_of_first_pairing
    (e : OpenPartialHomeomorph E2 M) {h : M → Real} {c r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2) (hrs : closedSquare r ⊆ e.source)
    (hform : ∀ x ∈ e.source, h (e x) = c - x 0 ^ 2 + x 1 ^ 2)
    (B : Fin 2 → Set M) (hB : ∀ i, IsConnected (B i))
    (hcover : (⋃ i, B i) = (h ⁻¹' {c + t}) \ e '' openSquare r)
    (k : Fin 2 × Fin 2 → Fin 2) (hb : ∀ j, e (movingContact r t j) ∈ B (k j))
    (hk : ∀ i j, k i = k j ↔ i.1 = j.1) :
    IsConnected (h ⁻¹' {c + t}) := by
  obtain ⟨E, hE⟩ := exists_equiv_of_four_contact_first_pairing k hk
  have hwhole : h ⁻¹' {c + t} =
      (⋃ i, positivePatchArc e r t i) ∪ ⋃ i, B (E i) := by
    rw [E.surjective.iUnion_comp, hcover]
    exact positive_level_eq_arcs_union_exterior e hr ht htr hrs hform
  rw [hwhole]
  exact isConnected_four_arc_resolution_crossed (positivePatchArc e r t) (fun i => B (E i))
    (fun j => e (movingContact r t (j.2, j.1)))
    (fun i => ((positivePatchArc_geometry e hr ht htr hrs).1 i).2) (fun i => hB (E i))
    (fun j => positive_contact_mem e hr ht htr (j.2, j.1))
    (fun j => hE (j.2, j.1) ▸ hb (j.2, j.1))

theorem negative_level_connected_of_second_pairing
    (e : OpenPartialHomeomorph E2 M) {h : M → Real} {c r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2) (hrs : closedSquare r ⊆ e.source)
    (hform : ∀ x ∈ e.source, h (e x) = c - x 0 ^ 2 + x 1 ^ 2)
    (B : Fin 2 → Set M) (hB : ∀ i, IsConnected (B i))
    (hcover : (⋃ i, B i) = (h ⁻¹' {c - t}) \ e '' openSquare r)
    (k : Fin 2 × Fin 2 → Fin 2) (hb : ∀ j, e (movingContact r (-t) j) ∈ B (k j))
    (hk : ∀ i j, k i = k j ↔ i.2 = j.2) :
    IsConnected (h ⁻¹' {c - t}) := by
  obtain ⟨E, hE⟩ := exists_equiv_of_four_contact_second_pairing k hk
  have hwhole : h ⁻¹' {c - t} =
      (⋃ i, negativePatchArc e r t i) ∪ ⋃ i, B (E i) := by
    rw [E.surjective.iUnion_comp, hcover]
    exact negative_level_eq_arcs_union_exterior e hr ht htr hrs hform
  rw [hwhole]
  exact isConnected_four_arc_resolution_crossed (negativePatchArc e r t) (fun i => B (E i))
    (fun j => e (movingContact r (-t) j))
    (fun i => ((negativePatchArc_geometry e hr ht htr hrs).1 i).2) (fun i => hB (E i))
    (fun j => negative_contact_mem e hr ht htr j) (fun j => hE j ▸ hb j)

variable [T2Space M]

theorem positive_level_two_components_of_second_pairing
    (e : OpenPartialHomeomorph E2 M) {h : M → Real} {c r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2) (hrs : closedSquare r ⊆ e.source)
    (hform : ∀ x ∈ e.source, h (e x) = c - x 0 ^ 2 + x 1 ^ 2)
    (B : Fin 2 → Set M) (hBc : ∀ i, IsClosed (B i)) (hB : ∀ i, IsConnected (B i))
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hcover : (⋃ i, B i) = (h ⁻¹' {c + t}) \ e '' openSquare r)
    (k : Fin 2 × Fin 2 → Fin 2) (hb : ∀ j, e (movingContact r t j) ∈ B (k j))
    (hk : ∀ i j, k i = k j ↔ i.2 = j.2) :
    ∃ E : Fin 2 ≃ Fin 2,
      (∀ i q, q ∈ positivePatchArc e r t i ∪ B (E i) →
        connectedComponentIn (h ⁻¹' {c + t}) q = positivePatchArc e r t i ∪ B (E i)) ∧
      Pairwise (fun i j => Disjoint (positivePatchArc e r t i ∪ B (E i))
        (positivePatchArc e r t j ∪ B (E j))) ∧
      Nat.card (ConnectedComponents (h ⁻¹' {c + t})) = 2 := by
  obtain ⟨E, hE⟩ := exists_equiv_of_four_contact_second_pairing k hk
  have hwhole : h ⁻¹' {c + t} =
      (⋃ i, positivePatchArc e r t i) ∪ ⋃ i, B (E i) := by
    rw [E.surjective.iUnion_comp, hcover]
    exact positive_level_eq_arcs_union_exterior e hr ht htr hrs hform
  have hgeom := positivePatchArc_geometry e hr ht htr hrs
  have hmeet (i j : Fin 2) : positivePatchArc e r t i ∩ B (E j) ⊆
      range (fun l : Fin 2 × Fin 2 => e (movingContact r t (l.2, l.1))) := by
    intro q hq
    have hext := hcover.subset (mem_iUnion_of_mem (E j) hq.2)
    obtain ⟨l, hl⟩ := positivePatchArc_inter_exterior_subset_contacts e hr ht htr i ⟨hq.1, hext⟩
    refine ⟨(l.1, Fin.rev l.2), ?_⟩
    simpa only [movingContact_eq_positive hr ht.le, Fin.rev_rev] using hl
  refine ⟨E, ?_⟩
  rw [hwhole]
  exact four_arc_resolution_parallel (positivePatchArc e r t) (fun i => B (E i))
    (fun j => e (movingContact r t (j.2, j.1)))
    (fun i => (hgeom.1 i).1.isClosed) (fun i => hBc (E i))
    (fun i => (hgeom.1 i).2) (fun i => hB (E i)) hgeom.2
    (fun i j hij => hBd (fun he => hij (E.injective he)))
    (fun j => positive_contact_mem e hr ht htr (j.2, j.1))
    (fun j => hE (j.2, j.1) ▸ hb (j.2, j.1)) hmeet

theorem negative_level_two_components_of_first_pairing
    (e : OpenPartialHomeomorph E2 M) {h : M → Real} {c r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2) (hrs : closedSquare r ⊆ e.source)
    (hform : ∀ x ∈ e.source, h (e x) = c - x 0 ^ 2 + x 1 ^ 2)
    (B : Fin 2 → Set M) (hBc : ∀ i, IsClosed (B i)) (hB : ∀ i, IsConnected (B i))
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hcover : (⋃ i, B i) = (h ⁻¹' {c - t}) \ e '' openSquare r)
    (k : Fin 2 × Fin 2 → Fin 2) (hb : ∀ j, e (movingContact r (-t) j) ∈ B (k j))
    (hk : ∀ i j, k i = k j ↔ i.1 = j.1) :
    ∃ E : Fin 2 ≃ Fin 2,
      (∀ i q, q ∈ negativePatchArc e r t i ∪ B (E i) →
        connectedComponentIn (h ⁻¹' {c - t}) q = negativePatchArc e r t i ∪ B (E i)) ∧
      Pairwise (fun i j => Disjoint (negativePatchArc e r t i ∪ B (E i))
        (negativePatchArc e r t j ∪ B (E j))) ∧
      Nat.card (ConnectedComponents (h ⁻¹' {c - t})) = 2 := by
  obtain ⟨E, hE⟩ := exists_equiv_of_four_contact_first_pairing k hk
  have hwhole : h ⁻¹' {c - t} =
      (⋃ i, negativePatchArc e r t i) ∪ ⋃ i, B (E i) := by
    rw [E.surjective.iUnion_comp, hcover]
    exact negative_level_eq_arcs_union_exterior e hr ht htr hrs hform
  have hgeom := negativePatchArc_geometry e hr ht htr hrs
  have hmeet (i j : Fin 2) : negativePatchArc e r t i ∩ B (E j) ⊆
      range (fun l : Fin 2 × Fin 2 => e (movingContact r (-t) l)) := by
    intro q hq
    have hext := hcover.subset (mem_iUnion_of_mem (E j) hq.2)
    obtain ⟨l, hl⟩ := negativePatchArc_inter_exterior_subset_contacts e hr ht htr i ⟨hq.1, hext⟩
    refine ⟨(l.1, Fin.rev l.2), ?_⟩
    simpa only [movingContact_eq_negative hr (neg_nonpos.mpr ht.le), neg_neg, Fin.rev_rev] using hl
  refine ⟨E, ?_⟩
  rw [hwhole]
  exact four_arc_resolution_parallel (negativePatchArc e r t) (fun i => B (E i))
    (fun j => e (movingContact r (-t) j))
    (fun i => (hgeom.1 i).1.isClosed) (fun i => hBc (E i))
    (fun i => (hgeom.1 i).2) (fun i => hB (E i)) hgeom.2
    (fun i j hij => hBd (fun he => hij (E.injective he)))
    (fun j => negative_contact_mem e hr ht htr j) (fun j => hE j ▸ hb j) hmeet

end Poincare.Manifold.Schoenflies.SaddleLevel
