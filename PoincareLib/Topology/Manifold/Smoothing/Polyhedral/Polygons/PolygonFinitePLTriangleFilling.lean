import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonFinitePLTriangleBoundary
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Disks.PolygonFinitePLDiskModel

/-!
# Controlled finite PL fillings into a triangle

A finite PL disk-pair model extends the prescribed finite PL
triangle boundary map. Exact boundary membership and the closing
edge parameter are retained. See Erickson pp. 8--10, Hudson 1969,
pp. 15--19 and M76 derivation 121.
-/

set_option autoImplicit false

open Set

namespace Polygon

/-- A polygon with a finite PL disk model can be mapped to
any independent triangle by a finite PL homeomorphism which
retains the exact closing-edge parameter and boundary.
See M76 derivation 121. -/
theorem exists_finitePL_triangle_filling {n : ℕ}
    (P : Polygon (ℝ × ℝ) (n + 3)) (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (hmodel : IsFinitePLBallPair (ℝ × ℝ) (closure P.inside) (P.boundary ℝ))
    (T : Polygon (ℝ × ℝ) 3) (hT : AffineIndependent ℝ T) :
    ∃ e : closure P.inside ≃ₜ convexHull ℝ (range T), e.IsFinitePL ∧
      (∀ x : closure P.inside, (x : ℝ × ℝ) ∈ P.boundary ℝ ↔
        (e x : ℝ × ℝ) ∈ frontier (convexHull ℝ (range T))) ∧
      (∀ (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1)
        (hx : AffineMap.lineMap (P (Fin.last (n + 2))) (P 0) t ∈ closure P.inside),
        (e ⟨AffineMap.lineMap (P (Fin.last (n + 2))) (P 0) t, hx⟩ : ℝ × ℝ) =
          AffineMap.lineMap (T 2) (T 0) t) := by
  obtain ⟨eb, heb, hb⟩ := P.exists_finitePL_triangle_boundary_model hP hinj T hT
  obtain ⟨e, hePL, he, hi⟩ :=
    hmodel.exists_extension (T.isFinitePLBallPair_convexHull_triangle hT) eb heb
  refine ⟨e, hePL, hi, ?_⟩
  intro t ht hx
  have hxb : AffineMap.lineMap (P (Fin.last (n + 2))) (P 0) t ∈ P.boundary ℝ := by
    apply mem_iUnion.mpr
    refine ⟨Fin.last (n + 2), t, ht, ?_⟩
    simp only [finRotate_last]
  exact (congrArg (fun z : convexHull ℝ (range T) => (z : ℝ × ℝ)) (he ⟨_, hxb⟩)).trans
    (hb t ht hxb)

end Polygon
