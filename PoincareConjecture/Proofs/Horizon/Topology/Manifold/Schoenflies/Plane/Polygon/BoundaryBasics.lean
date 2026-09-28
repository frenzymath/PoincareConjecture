import Mathlib.Geometry.Polygon.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Affine
import Mathlib.Topology.MetricSpace.Bounded

set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

theorem polygon_edgeSet_eq_segment (p : Polygon E n) (i : Fin n) :
    p.edgeSet ℝ i = segment ℝ (p i) (p (finRotate n i)) :=
  affineSegment_eq_segment ℝ _ _

theorem polygon_left_mem_edgeSet (p : Polygon E n) (i : Fin n) :
    p i ∈ p.edgeSet ℝ i := by
  rw [polygon_edgeSet_eq_segment]
  exact left_mem_segment ℝ _ _

theorem polygon_right_mem_edgeSet (p : Polygon E n) (i : Fin n) :
    p (finRotate n i) ∈ p.edgeSet ℝ i := by
  rw [polygon_edgeSet_eq_segment]
  exact right_mem_segment ℝ _ _

theorem polygon_edgeSet_subset_boundary (p : Polygon E n) (i : Fin n) :
    p.edgeSet ℝ i ⊆ p.boundary ℝ :=
  subset_iUnion (fun j => p.edgeSet ℝ j) i

theorem polygon_vertex_mem_boundary (p : Polygon E n) (i : Fin n) :
    p i ∈ p.boundary ℝ :=
  polygon_edgeSet_subset_boundary p i (polygon_left_mem_edgeSet p i)

theorem polygon_mem_boundary_iff (p : Polygon E n) (x : E) :
    x ∈ p.boundary ℝ ↔ ∃ i, x ∈ p.edgeSet ℝ i :=
  mem_iUnion

theorem polygon_edgeSet_isCompact (p : Polygon E n) (i : Fin n) :
    IsCompact (p.edgeSet ℝ i) := by
  rw [Polygon.edgeSet_eq_image_edgePath]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

theorem polygon_boundary_isCompact (p : Polygon E n) : IsCompact (p.boundary ℝ) :=
  isCompact_iUnion (polygon_edgeSet_isCompact p)

theorem polygon_boundary_isClosed (p : Polygon E n) : IsClosed (p.boundary ℝ) :=
  (polygon_boundary_isCompact p).isClosed

theorem polygon_boundary_isBounded (p : Polygon E n) :
    Bornology.IsBounded (p.boundary ℝ) :=
  (polygon_boundary_isCompact p).isBounded

theorem polygon_boundary_subset_convexHull (p : Polygon E n) :
    p.boundary ℝ ⊆ convexHull ℝ (range p) := by
  intro x hx
  obtain ⟨i, hi⟩ := (polygon_mem_boundary_iff p x).mp hx
  rw [polygon_edgeSet_eq_segment] at hi
  exact segment_subset_convexHull (mem_range_self i) (mem_range_self _) hi

theorem polygon_convexHull_boundary (p : Polygon E n) :
    convexHull ℝ (p.boundary ℝ) = convexHull ℝ (range p) := by
  apply subset_antisymm
  · exact convexHull_min (polygon_boundary_subset_convexHull p) (convex_convexHull ℝ _)
  · apply convexHull_mono
    rintro _ ⟨i, rfl⟩
    exact polygon_vertex_mem_boundary p i

theorem polygon_boundary_isPathConnected (p : Polygon E n) (hn : 0 < n) :
    IsPathConnected (p.boundary ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hvertices : ∀ i : Fin (m + 1), JoinedIn (p.boundary ℝ) (p 0) (p i) := by
    intro i
    induction i using Fin.induction with
    | zero => exact JoinedIn.refl (polygon_vertex_mem_boundary p 0)
    | succ i ih =>
      apply ih.trans
      apply JoinedIn.of_segment_subset
      have hrotate : finRotate (m + 1) i.castSucc = i.succ :=
        finRotate_of_lt i.isLt
      rw [← hrotate, ← polygon_edgeSet_eq_segment]
      exact polygon_edgeSet_subset_boundary p i.castSucc
  refine ⟨p 0, polygon_vertex_mem_boundary p 0, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := (polygon_mem_boundary_iff p x).mp hx
  apply (hvertices i).trans
  apply JoinedIn.of_segment_subset
  apply Subset.trans _ (polygon_edgeSet_subset_boundary p i)
  rw [polygon_edgeSet_eq_segment] at hi ⊢
  exact (convex_segment _ _).segment_subset (left_mem_segment ℝ _ _) hi

theorem polygon_boundary_isConnected (p : Polygon E n) (hn : 0 < n) :
    IsConnected (p.boundary ℝ) :=
  (polygon_boundary_isPathConnected p hn).isConnected

theorem polygon_boundary_isPreconnected (p : Polygon E n) :
    IsPreconnected (p.boundary ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa [Polygon.boundary] using (isPreconnected_empty : IsPreconnected (∅ : Set E))
  · exact (polygon_boundary_isConnected p hn).isPreconnected

end Poincare.Manifold.Schoenflies.Plane
