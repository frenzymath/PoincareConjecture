import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open Set

namespace Poincare.Topology

variable {X σ : Type*} [TopologicalSpace X] [Fintype σ]

theorem subset_interior_or_disjoint_of_disjoint_frontier {M D : Set X}
    (hM : IsPreconnected M) (hD : IsClosed D)
    (hfront : Disjoint M (frontier D)) : M ⊆ interior D ∨ Disjoint M D := by
  by_cases hmeet : (M ∩ D).Nonempty
  · left
    have hinside : M ∩ D ⊆ interior D := by
      intro x hx
      by_contra hi
      exact Set.disjoint_left.mp hfront hx.1
        (by rw [frontier, hD.closure_eq]; exact ⟨hx.2, hi⟩)
    apply hM.subset_of_closure_inter_subset isOpen_interior
    · obtain ⟨x, hx⟩ := hmeet
      exact ⟨x, hx.1, hinside hx⟩
    · intro x hx
      exact hinside ⟨hx.2, (closure_mono interior_subset).trans_eq hD.closure_eq hx.1⟩
  · right
    exact Set.disjoint_left.mpr (fun _ hx hy => hmeet ⟨_, hx, hy⟩)

theorem exists_finite_component_excision (M : σ → Set X) {D : Set X}
    (hD : IsClosed D) (hconn : ∀ i, IsPreconnected (M i))
    (hfront : ∀ i, Disjoint (M i) (frontier D))
    (hcomp : ∀ i, ∀ x ∈ M i, connectedComponentIn (⋃ j, M j) x = M i)
    (hmeet : ((⋃ i, M i) ∩ D).Nonempty) :
    ∃ J : Finset σ,
      J.card < Fintype.card σ ∧
      (∀ i, i ∈ J ↔ Disjoint (M i) D) ∧
      (⋃ i, M i) \ interior D = ⋃ i ∈ J, M i ∧
      (∀ i ∈ J, ∀ x ∈ M i,
        connectedComponentIn ((⋃ j, M j) \ interior D) x = M i) := by
  classical
  let J := Finset.univ.filter (fun i => Disjoint (M i) D)
  have hmem (i : σ) : i ∈ J ↔ Disjoint (M i) D := by simp [J]
  have hsub (i : σ) (hi : i ∈ J) : M i ⊆ (⋃ j, M j) \ interior D := by
    intro x hx
    exact ⟨mem_iUnion.mpr ⟨i, hx⟩,
      fun hxi => Set.disjoint_left.mp ((hmem i).mp hi) hx (interior_subset hxi)⟩
  refine ⟨J, ?_, hmem, ?_, ?_⟩
  · obtain ⟨x, hx, hxD⟩ := hmeet
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    have hi : i ∉ J := fun hi => Set.disjoint_left.mp ((hmem i).mp hi) hxi hxD
    have hproper : J ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _, fun h => hi (h.symm ▸ Finset.mem_univ i)⟩
    simpa only [Finset.card_univ] using Finset.card_lt_card hproper
  · ext x
    constructor
    · rintro ⟨hx, hxout⟩
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      have hi : i ∈ J := by
        apply (hmem i).mpr
        rcases subset_interior_or_disjoint_of_disjoint_frontier
            (hconn i) hD (hfront i) with hin | hout
        · exact (hxout (hin hxi)).elim
        · exact hout
      exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hxi⟩⟩
    · intro hx
      obtain ⟨i, hx⟩ := mem_iUnion.mp hx
      obtain ⟨hi, hxi⟩ := mem_iUnion.mp hx
      exact hsub i hi hxi
  · intro i hi x hx
    apply Set.Subset.antisymm
    · exact (connectedComponentIn_mono x sdiff_subset).trans_eq (hcomp i x hx)
    · exact (hconn i).subset_connectedComponentIn hx (hsub i hi)

end Poincare.Topology
