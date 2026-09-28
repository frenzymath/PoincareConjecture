import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.PolygonCellBoundaryNull













set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}





theorem m64_vertical_column_ae_of_cellwise
    {N : ℕ} (hN : 0 < N) {f : LoopPlane → M} {K : ℝ}
    (hcell : ∀ j : Fin N, ∀ p ∈ interior (m64PolygonCellSet j),
      g.tangentNorm (f p)
          (mfderiv (𝓡 2) (𝓡 n) f p
            (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ≤ K) :
    ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      g.tangentNorm (f p)
          (mfderiv (𝓡 2) (𝓡 n) f p
            (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ≤ K := by
  filter_upwards [m64_polygon_cells_interior_ae hN] with p hp
  obtain ⟨j, hj⟩ := hp
  exact hcell j p hj

end PoincareConjecture
