import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallPairs
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Disks.PolygonDiskModel

/-!
# Finite PL triangle disk models and cyclic relabeling

An independent triangle is its own finite PL convex-body model.
Cyclic relabeling preserves the exact carrier and boundary.
See Erickson pp. 8--10 and M76 derivation 121.
-/

set_option autoImplicit false

open Set

namespace Polygon

/-- An independent planar triangle is a finite PL ball pair
with its whole frontier. See M76 derivation 121. -/
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

/-- The canonical closed inside of a simple triangle is a
finite PL disk with the given polygon boundary.
See Erickson pp. 8--10 and M76 derivation 121. -/
theorem isFinitePLBallPair_triangle (P : Polygon (ℝ × ℝ) 3)
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) :
    IsFinitePLBallPair (ℝ × ℝ) (closure P.inside) (P.boundary ℝ) := by
  rw [← P.frontier_closure_inside hP hinj, P.closure_inside_triangle hP hinj]
  exact P.isFinitePLBallPair_convexHull_triangle (P.affineIndependent_triangle hP hinj)

/-- Cyclic relabeling preserves finite PL disk models of the
canonical polygon regions. See M76 derivation 121. -/
theorem isFinitePLBallPair_of_reindex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n : ℕ} (P : Polygon E n) (e : Fin m ≃ Fin n)
    (he : ∀ i, e (finRotate m i) = finRotate n (e i))
    (h : IsFinitePLBallPair (ℝ × ℝ) (closure (P.reindex e).inside) ((P.reindex e).boundary ℝ)) :
    IsFinitePLBallPair (ℝ × ℝ) (closure P.inside) (P.boundary ℝ) := by
  simpa only [P.inside_reindex e he, P.boundary_reindex e he] using h

end Polygon
