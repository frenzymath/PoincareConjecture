import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.SubdividedTriangleBoundary
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonBoundaryCoordinates
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.PolygonAffineImage
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineBasisEquivalence

/-!
# Triangle boundary models with a controlled closing edge

An affine change of reference triangle, followed by the cyclic
boundary correspondence, maps a polygon's closing edge onto
one prescribed triangle edge with its exact affine parameter.
See Erickson pp. 8--10 and M76 derivation 117.
-/

set_option autoImplicit false

open Set

namespace Polygon

/-- A simple polygon boundary can be identified with the
frontier of any independent planar triangle, preserving the
affine parameter on the closing edge and its exact membership.
See M76 derivation 117. -/
theorem exists_triangle_boundary_model {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
    (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (T : Polygon (ℝ × ℝ) 3) (hT : AffineIndependent ℝ T) :
    ∃ e : P.boundary ℝ ≃ₜ frontier (convexHull ℝ (range T)),
      (∀ (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1)
        (hx : AffineMap.lineMap (P (Fin.last (n + 2))) (P 0) t ∈ P.boundary ℝ),
        (e ⟨AffineMap.lineMap (P (Fin.last (n + 2))) (P 0) t, hx⟩ : ℝ × ℝ) =
          AffineMap.lineMap (T 2) (T 0) t) ∧
      (∀ x : P.boundary ℝ, (x : E) ∈ P.edgeSet ℝ (Fin.last (n + 2)) ↔
        (e x : ℝ × ℝ) ∈ segment ℝ (T 2) (T 0)) := by
  have hR := affineIndependent_referenceTriangle n
  let b : AffineBasis (Fin 3) ℝ (ℝ × ℝ) := ⟨referenceTriangle n, hR,
    hR.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [Module.finrank_prod])⟩
  let c : AffineBasis (Fin 3) ℝ (ℝ × ℝ) := ⟨T, hT,
    hT.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [Module.finrank_prod])⟩
  obtain ⟨A, hA⟩ := b.exists_affineEquiv_map c 0
  let a := A.toContinuousAffineEquiv
  let Q := (subdividedTriangle n).affineImage A.toAffineMap
  have hQ : Q.HasSimplicialEdges := hasSimplicialEdges_affineImage _
    (hasSimplicialEdges_subdividedTriangle n) A.toAffineMap A.injective
  have hiQ : Function.Injective Q := A.injective.comp (injective_subdividedTriangle n)
  have hfirst : Q 0 = T 0 := by
    change A (subdividedTriangle n 0) = T 0
    rw [show subdividedTriangle n 0 = (0, 0) by simp [subdividedTriangle]]
    exact hA 0
  have hlast : Q (Fin.last (n + 2)) = T 2 := by
    change A (subdividedTriangle n (Fin.last (n + 2))) = T 2
    rw [subdividedTriangle_last]
    exact hA 2
  have hhull : a '' convexHull ℝ (range (referenceTriangle n)) = convexHull ℝ (range T) := by
    change A.toAffineMap '' convexHull ℝ (range (referenceTriangle n)) = _
    rw [A.toAffineMap.image_convexHull, ← range_comp]
    have hfun : A.toAffineMap ∘ referenceTriangle n = T := by
      funext i
      exact hA i
    rw [hfun]
  have hfront : Q.boundary ℝ = frontier (convexHull ℝ (range T)) := by
    rw [affineImage_boundary, boundary_subdividedTriangle_eq_frontier]
    change a.toHomeomorph '' frontier (convexHull ℝ (range (referenceTriangle n))) = _
    rw [a.toHomeomorph.image_frontier]
    exact congrArg frontier hhull
  obtain ⟨e, hp, he⟩ := P.exists_boundary_homeomorph_edge_coordinates Q hP hQ hinj hiQ
  let H := e.trans (Homeomorph.setCongr hfront)
  have hval (x : P.boundary ℝ) : (H x : ℝ × ℝ) = (e x : ℝ × ℝ) := rfl
  refine ⟨H, ?_, ?_⟩
  · intro t ht hx
    rw [hval]
    simpa only [finRotate_last, hlast, hfirst] using
      hp (Fin.last (n + 2)) t ht (by simpa only [finRotate_last] using hx)
  · intro x
    rw [hval, he]
    simp only [edgeSet, finRotate_last, hlast, hfirst, affineSegment_eq_segment]

end Polygon
