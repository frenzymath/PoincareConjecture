import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPairs
import PoincareConjecture.Proofs.M76.Mathlib.UnitBallPairs
import PoincareConjecture.Proofs.M76.Mathlib.PolygonTriangleRegion
import PoincareConjecture.Proofs.M76.Mathlib.PolygonReindex

set_option autoImplicit false

open Set

namespace Polygon

theorem isFinitePLBallPair_convexHull_triangle (P : Polygon (ℝ × ℝ) 3)
    (hP : AffineIndependent ℝ P) :
    IsFinitePLBallPair (ℝ × ℝ) (convexHull ℝ (range P))
      (frontier (convexHull ℝ (range P))) := by
  classical
  let b : AffineBasis (Fin 3) ℝ (ℝ × ℝ) := ⟨P, hP,
    hP.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [Module.finrank_prod])⟩
  let V := Finset.univ.image P
  have hV : (V : Set (ℝ × ℝ)) = range P := by simp [V]
  have hVi : AffineIndependent ℝ ((↑) : V → ℝ × ℝ) := by
    change AffineIndependent ℝ ((↑) : ↥(V : Set (ℝ × ℝ)) → ℝ × ℝ)
    rw [hV]
    exact hP.range
  have hne : (interior (convexHull ℝ (V : Set (ℝ × ℝ)))).Nonempty := by
    rw [hV]
    exact ⟨_, b.centroid_mem_interior_convexHull⟩
  simpa only [hV] using isFinitePLBallPair_convexHull_finset V hVi hne

theorem isFinitePLBallPair_triangle (P : Polygon (ℝ × ℝ) 3)
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) :
    IsFinitePLBallPair (ℝ × ℝ) (closure P.inside) (P.boundary ℝ) := by
  rw [← P.frontier_closure_inside hP hinj, P.closure_inside_triangle hP hinj]
  exact P.isFinitePLBallPair_convexHull_triangle (P.affineIndependent_triangle hP hinj)

theorem isFinitePLBallPair_of_reindex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n : ℕ} (P : Polygon E n) (e : Fin m ≃ Fin n)
    (he : ∀ i, e (finRotate m i) = finRotate n (e i))
    (h : IsFinitePLBallPair (ℝ × ℝ) (closure (P.reindex e).inside) ((P.reindex e).boundary ℝ)) :
    IsFinitePLBallPair (ℝ × ℝ) (closure P.inside) (P.boundary ℝ) := by
  simpa only [P.inside_reindex e he, P.boundary_reindex e he] using h

end Polygon
