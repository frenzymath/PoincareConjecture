import PoincareLib.Topology.Manifold.Smoothing.Dehn.Annuli.Towers.CylinderLift
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.ConvexFrontierSubcomplex

/-!
# Finite complexes for the original annulus and its entire rim

The interval and its literal two-point frontier, multiplied by the original
square-rim polygon, construct both finite carriers required by the relative
boundary push. No triangulated annulus or marked carrier is assumed.
-/

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareMT.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

theorem exists_source_rim_complexes :
    ∃ K A : SimplicialComplex ℝ (V1 × V2),
      K.faces.Finite ∧ A.faces.Finite ∧ K.space = source ∧
      A.space = sphere (0 : V1) 1 ×ˢ Q2 ∧ A.space ⊆ K.space ∧ K.space.Nonempty := by
  obtain ⟨K, hK, hKs⟩ := exists_source_triangulation
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨I, hI, hIs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_unit_cube (ι := Fin 1)
  let B := I.frontierSubcomplex (closedBall (0 : V1) 1)
  have hB : B.faces.Finite := I.frontierSubcomplex_finite _ hI
  have hBs : B.space = sphere (0 : V1) 1 := by
    rw [I.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
      (by rw [interior_closedBall _ one_ne_zero]; exact ⟨0, mem_ball_self zero_lt_one⟩) hIs,
      frontier_closedBall _ one_ne_zero]
  let J := squareRimPolygon.simplicialComplex hasSimplicialEdges_squareRimPolygon
  have hJ : J.faces.Finite :=
    squareRimPolygon.finite_simplicialComplex_faces hasSimplicialEdges_squareRimPolygon
  have hJs : J.space = Q2 :=
    (squareRimPolygon.simplicialComplex_space hasSimplicialEdges_squareRimPolygon).trans
      boundary_squareRimPolygon
  obtain ⟨A, hA, hAs, _⟩ := B.exists_finite_triangulation_prod J hB hJ
  have hAs' : A.space = sphere (0 : V1) 1 ×ˢ Q2 := by rw [hAs, hBs, hJs]
  refine ⟨K, A, hK, hA, hKs, hAs', ?_, ?_⟩
  · rw [hAs', hKs]
    exact fun _ hx ↦ ⟨sphere_subset_closedBall hx.1, hx.2⟩
  · rw [hKs]
    exact ⟨(endpoint false, (squareRimBase : V2)),
      sphere_subset_closedBall (endpoint_mem_sphere false), squareRimBase.property⟩

end PoincareMT.M76.Dehn.ProtectedAnnulus
