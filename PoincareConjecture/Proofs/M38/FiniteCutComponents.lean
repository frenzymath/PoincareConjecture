import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Data.Finite.Sum

set_option autoImplicit false

open scoped Topology

universe u

namespace PoincareConjecture.M38

variable {A : Type u} [TopologicalSpace A] [LocallyConnectedSpace A]

theorem componentIn_eq_of_disjoint_frontier
    {K : Set A} (hK : IsClosed K) {x : A} (hx : x ∈ K)
    (hboundary : Disjoint (connectedComponentIn K x) (frontier K)) :
    connectedComponentIn K x = connectedComponent x := by
  have hinside : connectedComponentIn K x ⊆ interior K := by
    intro y hy
    by_contra hnot
    have hyK := connectedComponentIn_subset K x hy
    exact Set.disjoint_left.mp hboundary hy ⟨subset_closure hyK, hnot⟩
  have hinterior : connectedComponentIn K x = connectedComponentIn (interior K) x :=
    Set.Subset.antisymm
      (isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hx) hinside)
      (connectedComponentIn_mono x interior_subset)
  have hopen : IsOpen (connectedComponentIn K x) := by
    rw [hinterior]
    exact isOpen_interior.connectedComponentIn
  have hclosed : IsClosed (connectedComponentIn K x) := by
    rw [connectedComponentIn_eq_image hx]
    exact hK.isClosedMap_subtype_val _ isClosed_connectedComponent
  exact Set.Subset.antisymm
    (isPreconnected_connectedComponentIn.subset_connectedComponent (mem_connectedComponentIn hx))
    ((show IsClopen (connectedComponentIn K x) from ⟨hclosed, hopen⟩).connectedComponent_subset
      (mem_connectedComponentIn hx))

theorem finite_components_of_frontier_cover [CompactSpace A]
    {K : Set A} (hK : IsClosed K) {n : ℕ} (sphere : Fin n → Set A)
    (hconnected : ∀ i, IsConnected (sphere i))
    (hsubset : ∀ i, sphere i ⊆ K)
    (hfrontier : frontier K ⊆ ⋃ i, sphere i) : Finite (ConnectedComponents K) := by
  classical
  choose representative hrepresentative using
    (ConnectedComponents.surjective_coe :
      Function.Surjective (ConnectedComponents.mk : K → ConnectedComponents K))
  let region (q : ConnectedComponents K) := connectedComponentIn K (representative q).1
  have region_injective : Function.Injective region := by
    intro q r h
    change connectedComponentIn K (representative q).1 =
      connectedComponentIn K (representative r).1 at h
    rw [connectedComponentIn_eq_image (representative q).2,
      connectedComponentIn_eq_image (representative r).2] at h
    have hcomponents := Subtype.val_injective.image_injective h
    have hclasses := ConnectedComponents.coe_eq_coe.mpr hcomponents
    simpa only [hrepresentative] using hclasses
  have boundary_index (q : ConnectedComponents K)
      (h : ¬ Disjoint (region q) (frontier K)) : ∃ i, sphere i ⊆ region q := by
    obtain ⟨z, hzregion, hzfrontier⟩ := Set.not_disjoint_iff.mp h
    obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp (hfrontier hzfrontier)
    refine ⟨i, ?_⟩
    have hcomp := (hconnected i).isPreconnected.subset_connectedComponentIn hzi (hsubset i)
    have heq : region q = connectedComponentIn K z := connectedComponentIn_eq hzregion
    rwa [heq]
  let label (q : ConnectedComponents K) : Fin n ⊕ ConnectedComponents A :=
    if h : Disjoint (region q) (frontier K) then
      Sum.inr (ConnectedComponents.mk (representative q).1)
    else Sum.inl (Classical.choose (boundary_index q h))
  apply Finite.of_injective label
  intro q r hlabel
  by_cases hq : Disjoint (region q) (frontier K)
  · by_cases hr : Disjoint (region r) (frontier K)
    · simp only [label, dif_pos hq, dif_pos hr] at hlabel
      have hambient := ConnectedComponents.coe_eq_coe.mp (Sum.inr.inj hlabel)
      apply region_injective
      exact (componentIn_eq_of_disjoint_frontier hK (representative q).2 hq).trans
        (hambient.trans (componentIn_eq_of_disjoint_frontier hK (representative r).2 hr).symm)
    · simp [label, hq, hr] at hlabel
  · by_cases hr : Disjoint (region r) (frontier K)
    · simp [label, hq, hr] at hlabel
    · simp only [label, dif_neg hq, dif_neg hr] at hlabel
      have hi := Sum.inl.inj hlabel
      have hqsubset := Classical.choose_spec (boundary_index q hq)
      have hrsubset := Classical.choose_spec (boundary_index r hr)
      rw [← hi] at hrsubset
      obtain ⟨z, hz⟩ := (hconnected (Classical.choose (boundary_index q hq))).nonempty
      apply region_injective
      exact (connectedComponentIn_eq (hqsubset hz)).trans
        (connectedComponentIn_eq (hrsubset hz)).symm

end PoincareConjecture.M38
