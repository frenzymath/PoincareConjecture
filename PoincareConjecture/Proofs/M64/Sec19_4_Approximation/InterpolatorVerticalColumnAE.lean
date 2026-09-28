import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.PolygonCellEventually
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.PolygonCellBoundaryNull












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology Bundle ENNReal NNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]




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

end PoincareConjecture
