import PoincareConjecture.Proofs.M76.Mathlib.RadialFrontierConeBall
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLTriangleBoundary
import PoincareConjecture.Proofs.M76.Mathlib.PolygonSliceCoordinates

set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

theorem isFinitePLBallPair_radial_cone (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    {C : Set E} (hcv : Convex ℝ C) (hC0 : (0 : E) ∈ interior C)
    (hPC : P.boundary ℝ ⊆ frontier C) :
    IsFinitePLBallPair (ℝ × ℝ) (convexJoin ℝ {0} (P.boundary ℝ)) (P.boundary ℝ) := by
  let T := referenceTriangle 0
  have hT : AffineIndependent ℝ T := affineIndependent_referenceTriangle 0
  let b : AffineBasis (Fin 3) ℝ (ℝ × ℝ) := ⟨T, hT,
    hT.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [Module.finrank_prod])⟩
  obtain ⟨e, he, _⟩ := P.exists_finitePL_triangle_boundary_model hP hinj T hT
  exact he.isFinitePLBallPair_radial_cone hcv hC0 hPC
    ⟨P 0, P.vertex_mem_boundary 0⟩ ((finite_range T).isCompact_convexHull ℝ)
    (convex_convexHull ℝ _) ⟨_, b.centroid_mem_interior_convexHull⟩

end Polygon
