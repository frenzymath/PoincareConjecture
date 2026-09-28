import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SquareRimPolygon
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.UniformPolygonCorrespondence
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubsets

set_option autoImplicit false

open Set Metric Geometry Polygon

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1

theorem exists_square_polygon_boundary_coordinates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) :
    let U := squareRimPolygon.subdivide (uniformEdgeParameters (n + 2))
    let V := P.subdivide (uniformEdgeParameters 3)
    let hsize : 4 * (n + 3) = (n + 3) * 4 := Nat.mul_comm _ _
    ∃ e : Q ≃ₜ P.boundary ℝ, e.IsFinitePL ∧ (e squareRimBase : E) = P 0 ∧
      ∀ (i : Fin (4 * (n + 3))) (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1)
        (hx : AffineMap.lineMap (U i) (U (finRotate (4 * (n + 3)) i)) t ∈ Q),
        (e ⟨AffineMap.lineMap (U i) (U (finRotate (4 * (n + 3)) i)) t, hx⟩ : E) =
          AffineMap.lineMap (V (Fin.cast hsize i))
            (V (finRotate ((n + 3) * 4) (Fin.cast hsize i))) t := by
  let U := squareRimPolygon.subdivide (uniformEdgeParameters (n + 2))
  let V := P.subdivide (uniformEdgeParameters 3)
  let hsize : 4 * (n + 3) = (n + 3) * 4 := Nat.mul_comm _ _
  have hU := squareRimPolygon.hasSimplicialEdges_subdivide
    hasSimplicialEdges_squareRimPolygon injective_squareRimPolygon
    (uniformEdgeParameters (n + 2))
    (strictMono_uniformEdgeParameters _) (uniformEdgeParameters_zero _)
    (uniformEdgeParameters_last _)
  have hiU := squareRimPolygon.injective_subdivide
    hasSimplicialEdges_squareRimPolygon injective_squareRimPolygon
    (uniformEdgeParameters (n + 2))
    (strictMono_uniformEdgeParameters _) (uniformEdgeParameters_zero _)
    (uniformEdgeParameters_last _)
  have hUb : U.boundary ℝ = Q :=
    (squareRimPolygon.subdivide_boundary (uniformEdgeParameters (n + 2))
      (strictMono_uniformEdgeParameters _)
      (uniformEdgeParameters_zero _) (uniformEdgeParameters_last _)).trans
        boundary_squareRimPolygon
  have hV := P.hasSimplicialEdges_subdivide hP hinj (uniformEdgeParameters 3)
    (strictMono_uniformEdgeParameters _) (uniformEdgeParameters_zero _)
    (uniformEdgeParameters_last _)
  have hiV := P.injective_subdivide hP hinj (uniformEdgeParameters 3)
    (strictMono_uniformEdgeParameters _) (uniformEdgeParameters_zero _)
    (uniformEdgeParameters_last _)
  have hVb : V.boundary ℝ = P.boundary ℝ :=
    P.subdivide_boundary (uniformEdgeParameters 3) (strictMono_uniformEdgeParameters _)
      (uniformEdgeParameters_zero _) (uniformEdgeParameters_last _)
  obtain ⟨H, hH, hcoord⟩ := U.exists_finitePL_boundary_edge_coordinates_of_size_eq
    V hsize (by omega) hU hV hiU hiV
  let e := (Homeomorph.setCongr hUb.symm).trans (H.trans (Homeomorph.setCongr hVb))
  refine ⟨e, hH.setCongr hUb hVb, ?_, ?_⟩
  · have hu0 : U 0 = (squareRimBase : V2) := by
      change squareRimPolygon.subdivide (uniformEdgeParameters (n + 2)) 0 = _
      rw [subdivide_uniform_zero]
      rfl
    have hv0 : V 0 = P 0 := P.subdivide_uniform_zero 3
    have hzero := hcoord 0 0 (left_mem_Icc.mpr zero_le_one)
      (by rw [AffineMap.lineMap_apply_zero, hu0]; exact hUb.symm.subset squareRimBase.property)
    change (H ⟨(squareRimBase : V2), hUb.symm.subset squareRimBase.property⟩ : E) = P 0
    simpa only [AffineMap.lineMap_apply_zero, Fin.cast_zero, hu0, hv0] using hzero
  · intro i t ht hx
    exact hcoord i t ht (hUb.symm.subset hx)

end PoincareConjecture.M76.Dehn
