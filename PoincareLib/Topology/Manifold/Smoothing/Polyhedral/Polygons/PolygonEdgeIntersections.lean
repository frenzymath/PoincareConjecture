import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonExtremeVertex
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.DoubleCurve.PolygonCrossingIndex
import Mathlib.Order.Interval.Set.Infinite

/-!
# Unique edges at nonvertex polygon points

The simplicial intersection law and distinct cyclic labels make
each nonvertex boundary point belong to one edge. Nonvertical
edges contain points avoiding every vertex line. See Erickson,
Simple Polygons, Section 1.2, pp. 2--4 and M76 derivation 96.
-/

set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}

/-- A nonvertex point on a simple simplicial polygon cannot
belong to two different edges. See Erickson pp. 2--4 and
M76 derivation 96. -/
theorem eq_of_mem_edgeSets_of_not_vertex (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    {q : E} (hq : q ∉ range P) {i j : Fin (n + 3)}
    (hi : q ∈ P.edgeSet ℝ i) (hj : q ∈ P.edgeSet ℝ j) : i = j := by
  classical
  by_contra hij
  by_cases hnext : j = finRotate (n + 3) i
  · subst j
    have heq : q = P (finRotate (n + 3) i) := by
      have : q ∈ P.edgeSet ℝ i ∩ P.edgeSet ℝ (finRotate (n + 3) i) := ⟨hi, hj⟩
      rwa [P.adjacent_edgeSet_inter hP hinj i] at this
    exact hq ⟨_, heq.symm⟩
  · have hsubset : (P.edgeVertices i : Set E) ∩ P.edgeVertices j ⊆ {P i} := by
      intro x hx
      simp only [edgeVertices, Finset.coe_pair, mem_inter_iff, mem_insert_iff,
        mem_singleton_iff] at hx
      rcases hx.1 with rfl | rfl
      · exact mem_singleton _
      · rcases hx.2 with hj | hj
        · exact (hnext (hinj hj).symm).elim
        · exact (hij ((finRotate (n + 3)).injective (hinj hj))).elim
    have heq : q = P i := by
      have h := (convexHull_mono hsubset) (hP i j ⟨hi, hj⟩)
      simpa only [convexHull_singleton, mem_singleton_iff] using h
    exact hq ⟨i, heq.symm⟩

/-- Every nonvertical edge of a simple simplicial polygon has
a point on no vertex line and on no other edge. See Erickson
pp. 2--4 and M76 derivation 96. -/
theorem exists_regular_point_on_edge (P : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (hnv : P.HasNonverticalEdges) (i : Fin (n + 3)) :
    ∃ q ∈ P.edgeSet ℝ i,
      (∀ j, q.1 ≠ (P j).1) ∧ ∀ j, j ≠ i → q ∉ P.edgeSet ℝ j := by
  have hlt : min (P i).1 (P (finRotate (n + 3) i)).1 <
      max (P i).1 (P (finRotate (n + 3) i)).1 := min_lt_max.mpr (hnv i)
  obtain ⟨x, hx, hreg⟩ := ((Ioo_infinite hlt).sdiff
    (finite_range (fun j => (P j).1))).nonempty
  let q : ℝ × ℝ := (x, PlanarSegment.height (P i) (P (finRotate (n + 3) i)) x)
  have hq : q ∈ P.edgeSet ℝ i := by
    rw [edgeSet, affineSegment_eq_segment, PlanarSegment.mem_segment_iff (hnv i)]
    exact ⟨⟨hx.1.le, hx.2.le⟩, rfl⟩
  have hregular (j) : q.1 ≠ (P j).1 := fun h => hreg ⟨j, h.symm⟩
  refine ⟨q, hq, hregular, ?_⟩
  intro j hji hj
  have hqv : q ∉ range P := by
    rintro ⟨k, hk⟩
    exact hregular k (congrArg Prod.fst hk).symm
  exact hji (P.eq_of_mem_edgeSets_of_not_vertex hP hinj hqv hj hq)

end Polygon
