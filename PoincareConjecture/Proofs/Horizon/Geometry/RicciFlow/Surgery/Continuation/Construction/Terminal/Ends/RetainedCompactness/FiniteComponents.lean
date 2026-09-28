import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Connected.LocallyConnected










set_option autoImplicit false

open Set
open scoped Topology

namespace Poincare.Topology

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [LocallyConnectedSpace X] [PreconnectedSpace X]

omit [T2Space X] [PreconnectedSpace X] in
private theorem frontier_component_compl_subset {K : Set X} (hK : IsClosed K)
    {x : X} (hx : x ∈ Kᶜ) : frontier (connectedComponentIn Kᶜ x) ⊆ K := by
  intro y hy
  by_contra hyK
  have hmem : (⟨y, hyK⟩ : ↥(Kᶜ)) ∈ connectedComponent (⟨x, hx⟩ : ↥(Kᶜ)) := by
    rw [← (isClosed_connectedComponent (x := (⟨x, hx⟩ : ↥(Kᶜ)))).closure_eq]
    apply closure_subtype.mpr
    rw [← connectedComponentIn_eq_image hx]
    exact hy.1
  have hyC : y ∈ connectedComponentIn Kᶜ x := by
    rw [connectedComponentIn_eq_image hx]
    exact ⟨⟨y, hyK⟩, hmem, rfl⟩
  exact hy.2 (hK.isOpen_compl.connectedComponentIn.interior_eq.symm ▸ hyC)

omit [T2Space X] in

theorem component_compl_meets_frontier {K L : Set X}
    (hK : IsClosed K) (hKne : K.Nonempty)
    (hKL : K ⊆ interior L) {x : X} (hx : x ∉ L) :
    (connectedComponentIn Kᶜ x ∩ frontier L).Nonempty := by
  have hxK : x ∈ Kᶜ := fun h => hx (interior_subset (hKL h))
  let C := connectedComponentIn Kᶜ x
  have hCne : C.Nonempty := ⟨x, mem_connectedComponentIn hxK⟩
  have hCnot : C ≠ univ := by
    intro heq
    obtain ⟨p, hp⟩ := hKne
    exact connectedComponentIn_subset Kᶜ x (show p ∈ C from heq.symm ▸ mem_univ p) hp
  obtain ⟨p, hp⟩ := nonempty_frontier_iff.mpr ⟨hCne, hCnot⟩
  have hpL : p ∈ interior L := hKL (frontier_component_compl_subset hK hxK hp)
  obtain ⟨q, hqL, hqC⟩ := mem_closure_iff.mp hp.1 (interior L) isOpen_interior hpL
  by_contra h
  have hdis : Disjoint C (frontier L) := disjoint_iff_inter_eq_empty.mpr
    (not_nonempty_iff_eq_empty.mp h)
  have hsub := preconnected_subset_interior_of_disjoint_frontier
    isPreconnected_connectedComponentIn hdis ⟨q, hqC, hqL⟩
  exact hx (interior_subset (hsub (mem_connectedComponentIn hxK)))



theorem exists_finite_component_cover_outside_compact {K L : Set X}
    (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ interior L) :
    ∃ s : Finset X, (∀ p ∈ s, p ∈ Kᶜ) ∧
      ∀ x, x ∉ L → ∃ p ∈ s, x ∈ connectedComponentIn Kᶜ p := by
  classical
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · rw [hKe]
    by_cases hX : Nonempty X
    · let p := Classical.choice hX
      refine ⟨{p}, by simp, ?_⟩
      intro x hx
      exact ⟨p, by simp, by simp [connectedComponentIn_univ,
        PreconnectedSpace.connectedComponent_eq_univ]⟩
    · let : IsEmpty X := not_nonempty_iff.mp hX
      exact ⟨∅, by simp, fun x => isEmptyElim x⟩
  have hfront : IsCompact (frontier L) :=
    hL.of_isClosed_subset isClosed_frontier hL.isClosed.frontier_subset
  have hfrontK : frontier L ⊆ Kᶜ := fun p hp hpK => hp.2 (hKL hpK)
  obtain ⟨s, hs⟩ := hfront.elim_finite_subcover
    (fun p : frontier L => connectedComponentIn Kᶜ p.val)
    (fun _ => hK.isClosed.isOpen_compl.connectedComponentIn) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_connectedComponentIn (hfrontK hx)⟩)
  refine ⟨s.image Subtype.val, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
    exact hfrontK q.property
  · intro x hx
    obtain ⟨y, hyC, hyL⟩ := component_compl_meets_frontier hK.isClosed hKne hKL hx
    obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp (hs hyL)
    refine ⟨p.val, Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
    have heq := (connectedComponentIn_eq hyC).trans (connectedComponentIn_eq hyp).symm
    rw [← heq]
    exact mem_connectedComponentIn (fun hxK => hx (interior_subset (hKL hxK)))



theorem exists_unbounded_component_trace (K : CompactExhaustion X)
    {A : Set X} (hA : ∀ L : Set X, IsCompact L → ¬ A ⊆ L) (n : ℕ) :
    ∃ p : X, p ∈ (K n)ᶜ ∧
      ∀ L : Set X, IsCompact L → ¬ A ∩ connectedComponentIn (K n)ᶜ p ⊆ L := by
  classical
  obtain ⟨s, hs, hcover⟩ := exists_finite_component_cover_outside_compact
    (K.isCompact n) (K.isCompact (n + 1)) (K.subset_interior_succ n)
  by_contra h
  push Not at h
  choose L hL hsub using fun p : s => h p.val (hs p.val p.property)
  let B := K (n + 1) ∪ ⋃ p : s, L p
  have hB : IsCompact B := (K.isCompact (n + 1)).union (isCompact_iUnion hL)
  apply hA B hB
  intro x hxA
  by_cases hxK : x ∈ K (n + 1)
  · exact Or.inl hxK
  · obtain ⟨p, hp, hxp⟩ := hcover x hxK
    exact Or.inr (mem_iUnion.mpr ⟨⟨p, hp⟩, hsub ⟨p, hp⟩ ⟨hxA, hxp⟩⟩)

end Poincare.Topology
