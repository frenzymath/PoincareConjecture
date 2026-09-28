import PoincareConjecture.Proofs.M76.PrimeReduction.ReturningArcNesting
import Mathlib.Order.WellFoundedSet









set_option autoImplicit false

open Set

namespace Polygon

local notation "V" => (ℝ × ℝ)
local notation "Z" => (Set.preimage (Prod.snd : (ℝ × ℝ) → ℝ) ({0} : Set ℝ))




theorem exists_innermost_returning_bigon {ι : Type*} [Finite ι] [Nonempty ι]
    (n : ι → ℕ) (P : ∀ i, Polygon V (n i + 3))
    (hP : ∀ i, (P i).HasSimplicialEdges) (hi : ∀ i, Function.Injective (P i))
    (hup : ∀ i j, 0 ≤ (P i j).2)
    (A : ι → Set V) (u v : ι → V)
    (hA : ∀ i, IsFinitePLBallPair ℝ (A i) {u i, v i})
    (hboundary : ∀ i, (P i).boundary ℝ = A i ∪ segment ℝ (u i) (v i))
    (haxis : ∀ i, A i ∩ Z = {u i, v i})
    (hdis : Pairwise fun i j => Disjoint (A i) (A j)) :
    ∃ i, IsFinitePLBallPair V (closure (P i).inside) ((P i).boundary ℝ) ∧
      closure (P i).inside ∩ Z = segment ℝ (u i) (v i) ∧
      closure (P i).inside ∩ (⋃ j, (P j).boundary ℝ) = (P i).boundary ℝ ∧
      Disjoint (P i).inside (⋃ j, (P j).boundary ℝ) := by
  obtain ⟨s, hs⟩ := (finite_range (fun i => (P i).inside)).isPWO.exists_minimal
    (range_nonempty (fun i => (P i).inside))
  obtain ⟨i, rfl⟩ := hs.1
  have havoid (j : ι) : Disjoint (P i).inside ((P j).boundary ℝ) := by
    by_cases hij : i = j
    · subst j
      exact disjoint_left.mpr fun _ hx hb => hx.1 hb
    rcases (P i).returning_inside_subset_or_disjoint (P j) (hP i) (hi i)
        (hP j) (hi j) (hup i) (hboundary i) (hboundary j)
        (haxis i) (haxis j) (hA j) (hdis hij) with hsub | hd
    · have heq : (P i).inside = (P j).inside :=
        Subset.antisymm (hs.2 (mem_range_self j) hsub) hsub
      have hbound : (P i).boundary ℝ = (P j).boundary ℝ := by
        rw [← (P i).frontier_inside (hP i) (hi i),
          ← (P j).frontier_inside (hP j) (hi j), heq]
      obtain ⟨x, hxA, hxends⟩ := (hA j).sdiff_nonempty
      have hxP : x ∈ (P i).boundary ℝ := by
        rw [hbound, hboundary j]
        exact Or.inl hxA
      rcases (hboundary i) ▸ hxP with hxAi | hxseg
      · exact (disjoint_left.mp (hdis hij) hxAi hxA).elim
      · have hu : u i ∈ Z := ((haxis i).symm.subset (by simp)).2
        have hv : v i ∈ Z := ((haxis i).symm.subset (by simp)).2
        exact (hxends ((haxis j).subset
          ⟨hxA, segment_subset_returning_axis hu hv hxseg⟩)).elim
    · exact hd
  have hd : Disjoint (P i).inside (⋃ j, (P j).boundary ℝ) :=
    disjoint_iUnion_right.mpr havoid
  refine ⟨i, (P i).isFinitePLBallPair_closed_inside (hP i) (hi i),
    (P i).returning_closed_inside_axis (hP i) (hi i) (hup i) (hboundary i) (haxis i),
    ?_, hd⟩
  apply Subset.antisymm
  · rintro x ⟨hx, hxB⟩
    rw [closure_eq_self_union_frontier, (P i).frontier_inside (hP i) (hi i)] at hx
    exact hx.elim (fun hxi => (disjoint_left.mp hd hxi hxB).elim) id
  · intro x hx
    exact ⟨frontier_subset_closure ((P i).frontier_inside (hP i) (hi i) ▸ hx),
      mem_iUnion.mpr ⟨i, hx⟩⟩

end Polygon
