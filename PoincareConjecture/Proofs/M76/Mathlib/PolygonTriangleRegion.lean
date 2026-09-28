import PoincareConjecture.Proofs.M76.Mathlib.PolygonExtremeVertex
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionRecognition
import PoincareConjecture.Proofs.M76.Mathlib.SimplexIntrinsicFrontier
import PoincareConjecture.Proofs.M76.Mathlib.SimplexRelativeInteriorCoordinates

set_option autoImplicit false

open Set

namespace Polygon

theorem affineIndependent_triangle {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Polygon E 3) (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) :
    AffineIndependent ℝ P := by
  obtain ⟨_, i, _, _, hind⟩ := P.exists_nondegenerate_strict_max hP hinj
  have hfun : P.vertices = ![P 0, P 1, P 2] := List.ofFn_inj.mp rfl
  rw [hfun]
  fin_cases i
  · simpa [show (-1 : Fin 3) = 2 by decide] using hind.comm_left.comm_right
  · simpa using hind
  · simpa using hind.comm_right.comm_left

theorem frontier_convexHull_triangle (P : Polygon (ℝ × ℝ) 3)
    (hind : AffineIndependent ℝ P) : frontier (convexHull ℝ (range P)) = P.boundary ℝ := by
  let b : AffineBasis (Fin 3) ℝ (ℝ × ℝ) := ⟨P, hind,
    hind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [Module.finrank_prod])⟩
  have hi : intrinsicInterior ℝ (convexHull ℝ (range P)) =
      interior (convexHull ℝ (range P)) :=
    Subset.antisymm (fun _ hx => b.mem_interior_convexHull_of_mem_intrinsicInterior hx)
      interior_subset_intrinsicInterior
  have hf : intrinsicFrontier ℝ (convexHull ℝ (range P)) =
      frontier (convexHull ℝ (range P)) := by
    rw [← closure_sdiff_intrinsicInterior, hi, frontier]
  rw [← hf, StdSimplexCore.intrinsicFrontier_convexHull_range P hind]
  have himage (i : Fin 3) : P '' {j | j ≠ i} = (P.edgeVertices (finRotate 3 i) : Set (ℝ × ℝ)) := by
    fin_cases i <;> ext x <;> simp [edgeVertices, Fin.exists_fin_succ, eq_comm]
    tauto
  simp only [himage, ← P.edgeSet_eq_convexHull]
  exact (finRotate 3).surjective.iUnion_comp _

theorem closure_inside_triangle (P : Polygon (ℝ × ℝ) 3)
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) :
    closure P.inside = convexHull ℝ (range P) := by
  have hind := P.affineIndependent_triangle hP hinj
  let b : AffineBasis (Fin 3) ℝ (ℝ × ℝ) := ⟨P, hind,
    hind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [Module.finrank_prod])⟩
  apply P.closure_inside_eq_of_compact_convex hP hinj
    ((finite_range P).isCompact_convexHull ℝ) (convex_convexHull ℝ _)
  · exact ⟨_, b.centroid_mem_interior_convexHull⟩
  · exact P.frontier_convexHull_triangle hind

end Polygon
