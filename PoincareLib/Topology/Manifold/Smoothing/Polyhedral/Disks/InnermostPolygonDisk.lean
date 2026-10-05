import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.DisjointPolygonNesting
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Disks.PolygonFinitePLDisk
import Mathlib.Order.WellFoundedSet

/-!
# Innermost finite PL disk in a planar polygon family

In a nonempty finite family of disjoint simple polygon boundaries,
one canonical closed disk meets the whole family in precisely its
own boundary. See Alexander 1924, p. 7 and M76 derivation 122.
-/

set_option autoImplicit false

open Set

namespace Polygon

/-- A nonempty finite disjoint polygon family has an innermost
closed region meeting every other boundary trivially. Polygons
may have different vertex counts. See Alexander p. 7 and
M76 derivation 122. -/
theorem exists_innermost_closed_inside {ι : Type*} [Finite ι] [Nonempty ι]
    (n : ι → ℕ) (P : ∀ i, Polygon (ℝ × ℝ) (n i + 3))
    (hP : ∀ i, (P i).HasSimplicialEdges) (hinj : ∀ i, Function.Injective (P i))
    (hdisj : Pairwise (fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ))) :
    ∃ i, ∀ j, i ≠ j → Disjoint (closure (P i).inside) ((P j).boundary ℝ) := by
  obtain ⟨s, hs⟩ := (finite_range (fun i => closure (P i).inside)).isPWO.exists_minimal
    (range_nonempty (fun i => closure (P i).inside))
  obtain ⟨i, rfl⟩ := hs.1
  refine ⟨i, fun j hij => ?_⟩
  rcases (P i).boundary_subset_inside_or_outside_of_disjoint (P j)
    (hP i) (hinj i) (hP j) (hinj j) (hdisj hij) with hinside | houtside
  · have hsub := (P i).closure_inside_subset_inside_of_boundary_subset_inside (P j)
      (hP i) (hinj i) (hP j) (hinj j) hinside
    have hback : closure (P i).inside ⊆ closure (P j).inside :=
      hs.2 (mem_range_self j) (hsub.trans subset_closure)
    obtain ⟨x, hxb⟩ := ((P i).isConnected_boundary (hP i) (hinj i)).nonempty
    have hxcl : x ∈ closure (P i).inside := by
      rw [← (P i).frontier_inside (hP i) (hinj i)] at hxb
      exact frontier_subset_closure hxb
    exact ((hsub (hback hxcl)).1 hxb).elim
  · apply Set.disjoint_left.mpr
    intro x hx hxj
    rw [(P i).closure_inside (hP i) (hinj i)] at hx
    exact hx (houtside hxj)

/-- An innermost polygon bounds an actual finite PL disk whose
closed region meets the entire family in exactly its own boundary.
See Alexander p. 7 and M76 derivation 122. -/
theorem exists_innermost_finitePL_disk {ι : Type*} [Finite ι] [Nonempty ι]
    (n : ι → ℕ) (P : ∀ i, Polygon (ℝ × ℝ) (n i + 3))
    (hP : ∀ i, (P i).HasSimplicialEdges) (hinj : ∀ i, Function.Injective (P i))
    (hdisj : Pairwise (fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ))) :
    ∃ i, IsFinitePLBallPair (ℝ × ℝ) (closure (P i).inside) ((P i).boundary ℝ) ∧
      closure (P i).inside ∩ (⋃ j, (P j).boundary ℝ) = (P i).boundary ℝ ∧
      Disjoint (P i).inside (⋃ j, (P j).boundary ℝ) := by
  classical
  obtain ⟨i, hi⟩ := exists_innermost_closed_inside n P hP hinj hdisj
  have heq : closure (P i).inside ∩ (⋃ j, (P j).boundary ℝ) = (P i).boundary ℝ := by
    apply Subset.antisymm
    · rintro x ⟨hx, hxb⟩
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hxb
      by_cases hij : i = j
      · subst j
        exact hxj
      · exact (Set.disjoint_left.mp (hi j hij) hx hxj).elim
    · intro x hx
      refine ⟨?_, mem_iUnion.mpr ⟨i, hx⟩⟩
      rw [← (P i).frontier_inside (hP i) (hinj i)] at hx
      exact frontier_subset_closure hx
  refine ⟨i, (P i).isFinitePLBallPair_closed_inside (hP i) (hinj i), heq, ?_⟩
  apply Set.disjoint_left.mpr
  intro x hx hxb
  exact hx.1 (heq ▸ (show x ∈ closure (P i).inside ∩ (⋃ j, (P j).boundary ℝ) from
    ⟨subset_closure hx, hxb⟩))

end Polygon
