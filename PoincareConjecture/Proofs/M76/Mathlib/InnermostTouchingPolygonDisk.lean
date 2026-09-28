import PoincareConjecture.Proofs.M76.Mathlib.TouchingPolygonNesting
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLDisk
import Mathlib.Order.WellFoundedSet










set_option autoImplicit false

open Set

namespace Polygon




theorem exists_innermost_inside_of_singleton_inter {ι : Type*} [Finite ι] [Nonempty ι]
    (n : ι → ℕ) (P : ∀ i, Polygon (ℝ × ℝ) (n i + 3))
    (hP : ∀ i, (P i).HasSimplicialEdges) (hinj : ∀ i, Function.Injective (P i))
    (q : ℝ × ℝ)
    (hinter : Pairwise (fun i j => (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ {q})) :
    ∃ i, ∀ j, Disjoint (P i).inside ((P j).boundary ℝ) := by
  obtain ⟨s, hs⟩ := (finite_range (fun i => (P i).inside)).isPWO.exists_minimal
    (range_nonempty (fun i => (P i).inside))
  obtain ⟨i, rfl⟩ := hs.1
  refine ⟨i, fun j => ?_⟩
  by_cases hij : i = j
  · subst j
    exact Set.disjoint_left.mpr (fun _ hx hxb => hx.1 hxb)
  rcases (P i).inside_subset_or_disjoint_boundary_of_singleton_inter (P j)
      (hP i) (hinj i) (hP j) (hinj j) q (hinter hij) with hsub | hdisj
  · have hback : (P i).inside ⊆ (P j).inside := hs.2 (mem_range_self j) hsub
    have heq : (P i).inside = (P j).inside := Subset.antisymm hback hsub
    have hbound : (P i).boundary ℝ = (P j).boundary ℝ := by
      rw [← (P i).frontier_inside (hP i) (hinj i),
        ← (P j).frontier_inside (hP j) (hinj j), heq]
    obtain ⟨x, hx, hxq⟩ := ((P i).isConnected_boundary_sdiff_singleton (hP i) (hinj i) q).nonempty
    exact (hxq (hinter hij ⟨hx, hbound ▸ hx⟩)).elim
  · exact hdisj





theorem exists_innermost_finitePL_disk_of_singleton_inter {ι : Type*}
    [Finite ι] [Nonempty ι] (n : ι → ℕ) (P : ∀ i, Polygon (ℝ × ℝ) (n i + 3))
    (hP : ∀ i, (P i).HasSimplicialEdges) (hinj : ∀ i, Function.Injective (P i))
    (q : ℝ × ℝ)
    (hinter : Pairwise (fun i j => (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ {q})) :
    ∃ i, IsFinitePLBallPair (ℝ × ℝ) (closure (P i).inside) ((P i).boundary ℝ) ∧
      closure (P i).inside ∩ (⋃ j, (P j).boundary ℝ) = (P i).boundary ℝ ∧
      Disjoint (P i).inside (⋃ j, (P j).boundary ℝ) := by
  obtain ⟨i, hi⟩ := exists_innermost_inside_of_singleton_inter n P hP hinj q hinter
  have hd : Disjoint (P i).inside (⋃ j, (P j).boundary ℝ) := Set.disjoint_iUnion_right.mpr hi
  refine ⟨i, (P i).isFinitePLBallPair_closed_inside (hP i) (hinj i), ?_, hd⟩
  apply Subset.antisymm
  · rintro x ⟨hx, hxb⟩
    rw [closure_eq_self_union_frontier, (P i).frontier_inside (hP i) (hinj i)] at hx
    rcases hx with hxin | hxbound
    · exact (Set.disjoint_left.mp hd hxin hxb).elim
    · exact hxbound
  · intro x hx
    refine ⟨?_, mem_iUnion.mpr ⟨i, hx⟩⟩
    rw [← (P i).frontier_inside (hP i) (hinj i)] at hx
    exact frontier_subset_closure hx

end Polygon
