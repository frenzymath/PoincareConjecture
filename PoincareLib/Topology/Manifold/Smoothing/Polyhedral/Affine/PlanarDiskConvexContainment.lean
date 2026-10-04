import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.BoundedRegionBallInterior
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallImages
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonRegionRecognition
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.PolygonConvexContainment
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonSliceCoordinates
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineHyperplaneCoordinates

/-!
# Convex containment of actual planar finite PL disks

An actual finite PL disk with a simple polygon as its specified
boundary is the closed canonical inside of that polygon. Affine
plane coordinates therefore put every planar disk in any convex
set containing its boundary vertices, including an open convex
set. See Alexander 1924, pp. 6--8, Erickson, Simple Polygons,
pp. 8--9 and M76 derivation 278b.
-/

set_option autoImplicit false

open Set Geometry

namespace Set

/-- A finite PL disk in the real plane is exactly the closed
canonical inside of its specified simple polygon boundary.
See Alexander pp. 6--8 and M76 derivation 278b. -/
theorem IsFinitePLBallPair.eq_closure_polygon_inside {n : ℕ}
    {d : Set (ℝ × ℝ)} (P : Polygon (ℝ × ℝ) (n + 3))
    (hd : IsFinitePLBallPair (ℝ × ℝ) d (P.boundary ℝ))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) :
    d = closure P.inside := by
  rw [P.inside_eq_of_open_bounded_frontier hP hinj isOpen_interior
    (hd.isCompact.isBounded.subset interior_subset)
    (hd.isConnected_interior_of_finrank_eq rfl).nonempty
    (hd.frontier_interior_of_finrank_eq rfl)]
  exact (hd.closure_interior_of_finrank_eq rfl).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Every actual finite PL disk in a nonconstant affine plane
of a three-dimensional space lies in any convex set containing
its simple polygon's vertices. The convex set need not be closed.
See Alexander pp. 6--8 and M76 derivation 278b. -/
theorem IsFinitePLBallPair.subset_convex_of_planar_polygon_boundary {n : ℕ}
    {d C : Set E} (P : Polygon E (n + 3))
    (hd : IsFinitePLBallPair (ℝ × ℝ) d (P.boundary ℝ))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0) (hdim : Module.finrank ℝ E = 3)
    (hdplane : d ⊆ {x | A x = 0}) (hC : Convex ℝ C) (hPC : range P ⊆ C) :
    d ⊆ C := by
  obtain ⟨a, r, _, hright, _⟩ := A.exists_zeroLevel_coordinates hA
    (F := ℝ × ℝ) (by simp [hdim, Module.finrank_prod])
  let Q := P.affineImage r.toAffineMap
  have hQ := P.affineImage_of_leftInvOn hP hinj r.toAffineMap a.toAffineMap
    (fun x hx => hright (hdplane (hd.1 hx)))
  have hdQ : IsFinitePLBallPair (ℝ × ℝ) (r '' d) (Q.boundary ℝ) := by
    simpa only [Q, Polygon.affineImage_boundary, ContinuousAffineMap.coe_toAffineMap] using
      hd.affine_image r (hright.injOn.mono hdplane)
  have heq := hdQ.eq_closure_polygon_inside Q hQ.2.1 hQ.1
  have hvertices : range Q ⊆ a ⁻¹' C := by
    rintro y ⟨i, rfl⟩
    change a (r (P i)) ∈ C
    rw [hright (hdplane (hd.1 (P.vertex_mem_boundary i)))]
    exact hPC (mem_range_self i)
  have hinside := Q.closure_inside_subset_convex hQ.2.1 hQ.1
    (hC.affine_preimage a.toAffineMap) hvertices
  intro x hx
  have hax := hinside (heq.subset (mem_image_of_mem r hx))
  change a (r x) ∈ C at hax
  rwa [hright (hdplane hx)] at hax

end Set
