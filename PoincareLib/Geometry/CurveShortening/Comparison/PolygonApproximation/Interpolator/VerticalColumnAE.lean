import PoincareLib.Geometry.CurveShortening.Comparison.PolygonApproximation.Polygon.CellEventually
import PoincareLib.Geometry.CurveShortening.Comparison.PolygonApproximation.Polygon.CellBoundaryNull

/-!
# AE vertical-column transport for the interpolator

The smooth side extension has a cellwise vertical-column estimate.  This
adapter transports that estimate to the assembled interpolator map, using the
finite polygon-cell interior cover and eventual equality away from the cuts.

Morgan--Tian context: Section 19.4, Definition 19.18 and Claims 19.19-19.22, printed pp.
450-453.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology Bundle ENNReal NNReal

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

/-- Transfer vertical-column bounds from cell extensions to the assembled map off the null
cuts. Source: Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp. 450-453;
project construction in `proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64_interpolator_vertical_column_ae_of_cell_extensions
    {g : RiemannianMetric n M} {D : LeviCivitaData g}
    {N : ℕ} (hN : 0 < N)
    (polygon : M63GeodesicPolygon g D N)
    {gamma : ℝ → M} {H : ℝ × (M × M) → M}
    {f : LoopPlane → M} {K : ℝ}
    (hf : f = (fun p : LoopPlane =>
      H (p 1, gamma (p 0), polygon.map (p 0))))
    (hcolumn : ∀ j : Fin N, ∀ z ∈ interior (m64PolygonCellSet j),
      g.tangentNorm
          (H (z 1, gamma (z 0),
            (polygon.side j).map (z 0 - m63CellLeft N j)))
          (mfderiv (𝓡 2) (𝓡 n)
            (fun p : LoopPlane => H (p 1, gamma (p 0),
              (polygon.side j).map (p 0 - m63CellLeft N j))) z
            (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ≤ K) :
    ∀ᵐ z ∂volume.restrict m64AnnulusDomain,
      g.tangentNorm (f z)
          (mfderiv (𝓡 2) (𝓡 n) f z
            (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ≤ K := by
  filter_upwards [m64_polygon_cells_interior_ae hN] with z hz
  obtain ⟨j, hzj⟩ := hz
  have hevent0 :=
    m64_interpolator_map_eventuallyEq_cell_extension
      (gamma := gamma) (H := H) polygon j hzj
  have hevent : f =ᶠ[𝓝 z]
      (fun p : LoopPlane => H (p 1, gamma (p 0),
        (polygon.side j).map (p 0 - m63CellLeft N j))) := by
    rw [hf]
    exact hevent0
  have hvalue : f z = H (z 1, gamma (z 0),
      (polygon.side j).map (z 0 - m63CellLeft N j)) := hevent.self_of_nhds
  have hderiv : mfderiv (𝓡 2) (𝓡 n) f z =
      mfderiv (𝓡 2) (𝓡 n)
        (fun p : LoopPlane => H (p 1, gamma (p 0),
          (polygon.side j).map (p 0 - m63CellLeft N j))) z :=
    hevent.mfderiv_eq
  rw [hvalue, hderiv]
  exact hcolumn j z hzj

end PoincareMT
