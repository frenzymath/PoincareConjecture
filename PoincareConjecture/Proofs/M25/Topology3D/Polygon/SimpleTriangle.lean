import PoincareConjecture.Proofs.M25.Topology3D.Polygon.SimplePolygon
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.TriangleBase
import Mathlib.Analysis.Convex.Between












set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {p : Polygon E 3}


theorem IsSimplePolygon.triangle_affineIndependent (hp : IsSimplePolygon p) :
    AffineIndependent ℝ p := by
  apply (affineIndependent_iff_not_collinear_of_ne (p := p)
    (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)
    (by decide : (1 : Fin 3) ≠ 2)).2
  intro hcol
  rcases hcol.wbtw_or_wbtw_or_wbtw with h | h | h
  · have heq := (hp.vertex_mem_edgeSet_iff 1 2).mp (by
      simpa [polygon_edgeSet_eq_segment] using h.symm.mem_segment)
    exact (by decide : ¬((1 : Fin 3) = 2 ∨ 1 = finRotate 3 2)) heq
  · have heq := (hp.vertex_mem_edgeSet_iff 2 0).mp (by
      simpa [polygon_edgeSet_eq_segment] using h.symm.mem_segment)
    exact (by decide : ¬((2 : Fin 3) = 0 ∨ 2 = finRotate 3 0)) heq
  · have heq := (hp.vertex_mem_edgeSet_iff 0 1).mp (by
      simpa [polygon_edgeSet_eq_segment] using h.symm.mem_segment)
    exact (by decide : ¬((0 : Fin 3) = 1 ∨ 0 = finRotate 3 1)) heq

variable [FiniteDimensional ℝ E]


def IsSimplePolygon.triangleAffineBasis (hp : IsSimplePolygon p)
    (hdim : Module.finrank ℝ E = 2) : AffineBasis (Fin 3) ℝ E where
  toFun := p
  ind' := hp.triangle_affineIndependent
  tot' := hp.triangle_affineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
    (by simp [hdim])


theorem IsSimplePolygon.triangle_boundary_eq_frontier (hp : IsSimplePolygon p)
    (hdim : Module.finrank ℝ E = 2) :
    p.boundary ℝ = frontier (convexHull ℝ (range p)) :=
  affineBasisTriangle_boundary_eq_frontier (hp.triangleAffineBasis hdim)



theorem IsSimplePolygon.triangle_homeomorph (hp : IsSimplePolygon p)
    (hdim : Module.finrank ℝ E = 2) :
    ∃ h : E ≃ₜ E, h '' interior (convexHull ℝ (range p)) = ball 0 1 ∧
      h '' convexHull ℝ (range p) = closedBall 0 1 ∧
      h '' p.boundary ℝ = sphere 0 1 :=
  affineBasisTriangle_homeomorph (hp.triangleAffineBasis hdim)

end PoincareConjecture.M25.Topology3D
