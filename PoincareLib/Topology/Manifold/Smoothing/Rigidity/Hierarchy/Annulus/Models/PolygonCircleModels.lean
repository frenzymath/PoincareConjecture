import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Models.LineStarCircles
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonFinitePLTriangleBoundary
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Boundary.Circles.StandardCircleOrder
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Annuli.Surfaces.Cuts.RimSubcomplexes

/-!
# Finite PL circle subcomplexes of an actual polygonal rim

Triangle boundary coordinates compare every simple polygon with the
standard square circle. A disjoint polygon presentation then partitions
the original finite rim complex, with exact coverage of all its faces.
-/

set_option autoImplicit false
open Set Metric Geometry

namespace Polygon

theorem exists_finitePL_square_circle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hi : Function.Injective P) :
    ∃ gamma : sphere (0 : Fin 2 → ℝ) 1 ≃ₜ P.boundary ℝ, gamma.IsFinitePL := by
  have hball : IsFinitePLBallPair (ℝ × ℝ)
      (closedBall (0 : Fin 2 → ℝ) 1) (sphere (0 : Fin 2 → ℝ) 1) :=
    (isFinitePLBallPair_unit_cube (ι := Fin 2)).model_equiv
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  obtain ⟨m, Q, hQi, hQ, hQs⟩ := hball.exists_polygon_boundary
  obtain ⟨A, hA, _⟩ := P.exists_finitePL_triangle_boundary_model hP hi
    (referenceTriangle 0) (affineIndependent_referenceTriangle 0)
  obtain ⟨B, hB, _⟩ := Q.exists_finitePL_triangle_boundary_model hQ hQi
    (referenceTriangle 0) (affineIndependent_referenceTriangle 0)
  exact ⟨(Homeomorph.setCongr hQs.symm).trans (B.trans A.symm),
    (hB.setCongr hQs rfl).trans hA.symm⟩

end Polygon

namespace Geometry.SimplicialComplex

theorem exists_circle_subcomplexes_of_polygon_presentation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (h : HasDisjointPolygonPresentation K.space) :
    ∃ (m : ℕ) (J : Fin m → SimplicialComplex ℝ E)
      (gamma : ∀ i, sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (J i).space),
      (∀ i, J i ≤ K ∧ (J i).faces.Finite ∧ (gamma i).IsFinitePL) ∧
      Pairwise (fun i j => Disjoint (J i).space (J j).space) ∧
      (⋃ i, (J i).space) = K.space ∧
      ∀ t, t ∈ K.faces ↔ ∃ i, t ∈ (J i).faces := by
  classical
  obtain ⟨m, n, P, hP, hcover, hdis⟩ := h
  have hclosed (i : Fin m) : IsClosed ((P i).boundary ℝ) :=
    (P i).isCompact_boundary.isClosed
  obtain ⟨J, hJK, hJs, hfaces⟩ :=
    PoincareMT.M76.Dehn.Annuli.exists_subcomplexes_of_disjoint_closed_cover K hK
      (fun i => (P i).boundary ℝ) hclosed hdis hcover.symm
  have hex (i : Fin m) : ∃ gamma : sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (J i).space,
      gamma.IsFinitePL := by
    obtain ⟨gamma, hg⟩ := (P i).exists_finitePL_square_circle (hP i).2 (hP i).1
    exact ⟨gamma.trans (Homeomorph.setCongr (hJs i).symm), hg.setCongr rfl (hJs i).symm⟩
  choose gamma hg using hex
  refine ⟨m, J, gamma, fun i => ⟨hJK i, hK.subset (hJK i), hg i⟩, ?_, ?_, hfaces⟩
  · intro i j hij
    simpa only [hJs] using hdis hij
  · simpa only [hJs] using hcover.symm

end Geometry.SimplicialComplex
