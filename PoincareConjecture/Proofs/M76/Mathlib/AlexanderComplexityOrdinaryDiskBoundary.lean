import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLDiskModel
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLImage
import PoincareConjecture.Proofs.M76.Mathlib.SubdividedTriangleBoundary









set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem IsFinitePLBallPair.exists_polygon_boundary {d b : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) :
    ∃ (n : ℕ) (P : Polygon E (n + 3)),
      Function.Injective P ∧ P.HasSimplicialEdges ∧ P.boundary ℝ = b := by
  let T := Polygon.referenceTriangle 0
  let P := Polygon.subdividedTriangle 0
  let C : Set (ℝ × ℝ) := convexHull ℝ (range T)
  have hT : AffineIndependent ℝ T := Polygon.affineIndependent_referenceTriangle 0
  have hC : IsFinitePLBallPair (ℝ × ℝ) C (frontier C) :=
    T.isFinitePLBallPair_convexHull_triangle hT
  have hPb : P.boundary ℝ = frontier C :=
    Polygon.boundary_subdividedTriangle_eq_frontier 0
  have hPC : P.boundary ℝ ⊆ C := by
    rw [hPb]
    exact ((finite_range T).isCompact_convexHull ℝ).isClosed.frontier_subset
  obtain ⟨e, he, heb⟩ := hC.exists_homeomorph hd
  obtain ⟨f, hf, hef⟩ := he
  have hfi : InjOn f C := by
    intro x hx y hy hxy
    have hexy : e ⟨x, hx⟩ = e ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa only [hef] using hxy
    exact congrArg Subtype.val (e.injective hexy)
  have himage : f '' P.boundary ℝ = b := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hef ⟨x, hPC hx⟩]
      exact (heb ⟨x, hPC hx⟩).mp (hPb.subset hx)
    · intro hy
      let x : C := e.symm ⟨y, hd.1 hy⟩
      have hex : e x = ⟨y, hd.1 hy⟩ := e.apply_symm_apply _
      have hx : (x : ℝ × ℝ) ∈ P.boundary ℝ := by
        rw [hPb]
        apply (heb x).mpr
        simpa only [hex] using hy
      refine ⟨x, hx, ?_⟩
      rw [← hef x, hex]
  obtain ⟨n, Q, hQi, hQe, hQb⟩ := P.exists_polygon_finitePL_image
    (Polygon.hasSimplicialEdges_subdividedTriangle 0)
    (Polygon.injective_subdividedTriangle 0) hf hPC (hfi.mono hPC)
  exact ⟨n, Q, hQi, hQe, hQb.trans himage⟩

end Set
