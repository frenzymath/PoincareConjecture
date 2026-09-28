import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.CellLipschitzAssembly
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.PolygonCellCompact
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.MetricLipschitzBridge












set_option autoImplicit false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology Bundle ENNReal NNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]




theorem m64_polygon_cell_lipschitz_of_extension
    (g : RiemannianMetric n M) {f F : LoopPlane → M}
    {N : ℕ} (hN : 0 < N) (j : Fin N)
    (hcontinuous : ContinuousOn f m64AnnulusDomain)
    (hF : ∀ x ∈ m64PolygonCellSet j,
      ContMDiffAt (𝓡 2) (𝓡 n) 1 F x)
    (hEq : EqOn f F (m64PolygonCellSet j)) :
    ∃ K : ℝ≥0, ∀ x ∈ m64PolygonCellSet j, ∀ y ∈ m64PolygonCellSet j,
      g.edist (f x) (f y) ≤
        (K : ℝ≥0∞) * ENNReal.ofReal ‖x - y‖ := by
  let S := m64PolygonCellSet j
  have hsub : S ⊆ m64AnnulusDomain :=
    m64PolygonCellSet_subset_annulusDomain hN j
  have hfinite : ∀ x ∈ S, ∀ y ∈ S,
      g.edist (f x) (f y) ≠ (⊤ : ENNReal) := by
    intro x hx y hy
    exact m64AnnulusDomain_edist_ne_top g hcontinuous x (hsub hx) y (hsub hy)
  obtain ⟨K, hK⟩ := m64_lipschitzOn_cell_of_extension g
    (m64PolygonCellSet_isCompact hN j) hfinite hF hEq
  exact ⟨K, hK⟩

end PoincareConjecture
