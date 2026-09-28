import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood
import Mathlib.Order.Preorder.Finite
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D
namespace BallNeighborhoodChart

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [ProperSpace E] in

theorem boundary_connected (B : BallNeighborhoodChart E F)
    (hdim : 1 < Module.rank ℝ E) : IsConnected B.boundary :=
  (isConnected_sphere hdim 0 zero_le_one).image B.chart
    (B.chart.continuousOn.mono
      (Metric.sphere_subset_closedBall.trans B.closedBall_subset_source))

theorem preconnected_subset_inside_or_outside (B : BallNeighborhoodChart E F)
    {A : Set F} (hA : IsPreconnected A) (hdis : Disjoint A B.boundary) :
    A ⊆ B.inside ∨ A ⊆ B.closedRegionᶜ := by
  apply hA.subset_or_subset B.inside_open B.closedRegion_compact.isClosed.isOpen_compl
  · apply Set.disjoint_left.mpr
    intro y hy hyo
    apply hyo
    rw [← B.inside_union_boundary]
    exact Or.inl hy
  · intro y hy
    by_cases hiy : y ∈ B.inside
    · exact Or.inl hiy
    · refine Or.inr ?_
      intro hky
      rw [← B.inside_union_boundary] at hky
      exact hky.elim hiy (Set.disjoint_left.mp hdis hy)

variable [Nontrivial F]

theorem not_mutual_boundary_inside (A B : BallNeighborhoodChart E F) :
    ¬(B.boundary ⊆ A.inside ∧ A.boundary ⊆ B.inside) := by
  rintro ⟨hBA, hAB⟩
  have hclosed : IsClosed (A.inside ∪ B.inside) := by
    apply isClosed_of_closure_subset
    rw [closure_union, A.closure_inside, B.closure_inside,
      ← A.inside_union_boundary, ← B.inside_union_boundary]
    intro y hy
    rcases hy with (hy | hy) | (hy | hy)
    · exact Or.inl hy
    · exact Or.inr (hAB hy)
    · exact Or.inr hy
    · exact Or.inl (hBA hy)
  have huniv : A.inside ∪ B.inside = univ :=
    (show IsClopen (A.inside ∪ B.inside) from
      ⟨hclosed, A.inside_open.union B.inside_open⟩).eq_univ
      (A.inside_connected.nonempty.mono subset_union_left)
  apply NormedSpace.unbounded_univ ℝ F
  rw [← huniv]
  exact A.inside_bounded.union B.inside_bounded

theorem closedRegion_subset_inside_of_boundary_subset
    (A B : BallNeighborhoodChart E F)
    (hAc : IsPreconnected A.boundary) (hBc : IsConnected B.boundary)
    (hdis : Disjoint A.boundary B.boundary) (hBA : B.boundary ⊆ A.inside) :
    B.closedRegion ⊆ A.inside := by
  have hAo : A.boundary ⊆ B.closedRegionᶜ :=
    (B.preconnected_subset_inside_or_outside hAc hdis).resolve_left
      (fun hAB => A.not_mutual_boundary_inside B ⟨hBA, hAB⟩)
  have hBdis : Disjoint B.inside A.boundary := by
    apply Set.disjoint_left.mpr
    intro y hyB hyA
    apply hAo hyA
    rw [← B.inside_union_boundary]
    exact Or.inl hyB
  have hmeet : (A.inside ∩ B.inside).Nonempty := by
    obtain ⟨p, hp⟩ := hBc.nonempty
    have hpcl : p ∈ closure B.inside := by
      rw [B.closure_inside, ← B.inside_union_boundary]
      exact Or.inr hp
    exact mem_closure_iff.mp hpcl A.inside A.inside_open (hBA hp)
  have hBi : B.inside ⊆ A.inside := by
    rcases A.preconnected_subset_inside_or_outside
        B.inside_connected.isPreconnected hBdis with hi | ho
    · exact hi
    · obtain ⟨p, hpA, hpB⟩ := hmeet
      exact False.elim (ho hpB (by
        rw [← A.inside_union_boundary]
        exact Or.inl hpA))
  rw [← B.inside_union_boundary]
  exact union_subset hBi hBA

theorem exists_innermost {ι : Type*} [Finite ι] [Nonempty ι]
    (B : ι → BallNeighborhoodChart E F)
    (hc : ∀ i, IsConnected (B i).boundary)
    (hdis : ∀ i j, i ≠ j → Disjoint (B i).boundary (B j).boundary) :
    ∃ i, (∀ j, Disjoint (B i).inside (B j).boundary) ∧
      (B i).closedRegion ∩ (⋃ j, (B j).boundary) = (B i).boundary := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨i, hi⟩ := Finset.exists_minimalFor (fun i => (B i).inside)
    Finset.univ Finset.univ_nonempty
  have hinside (j : ι) : Disjoint (B i).inside (B j).boundary := by
    by_cases hij : i = j
    · subst j
      exact (B i).inside_disjoint_boundary
    · apply Set.disjoint_left.mpr
      intro y hyi hyj
      have hji : (B j).boundary ⊆ (B i).inside := by
        rcases (B i).preconnected_subset_inside_or_outside
            (hc j).isPreconnected (hdis j i (Ne.symm hij)) with hin | hout
        · exact hin
        · exact False.elim (hout hyj (by
            rw [← (B i).inside_union_boundary]
            exact Or.inl hyi))
      have hsub := (B i).closedRegion_subset_inside_of_boundary_subset (B j)
        (hc i).isPreconnected (hc j) (hdis i j hij) hji
      have hreverse : (B i).inside ⊆ (B j).inside :=
        hi.2 (Finset.mem_univ j) (fun z hz => hsub (by
          rw [← (B j).inside_union_boundary]
          exact Or.inl hz))
      exact Set.disjoint_left.mp (B j).inside_disjoint_boundary (hreverse hyi) hyj
  refine ⟨i, hinside, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hyU⟩
    rw [← (B i).inside_union_boundary] at hy
    rcases hy with hy | hy
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hyU
      exact False.elim (Set.disjoint_left.mp (hinside j) hy hj)
    · exact hy
  · intro hy
    refine ⟨?_, mem_iUnion.mpr ⟨i, hy⟩⟩
    rw [← (B i).inside_union_boundary]
    exact Or.inr hy

end BallNeighborhoodChart
end PoincareConjecture.M25.Topology3D
