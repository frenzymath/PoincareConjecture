import PoincareLib.Geometry.Riemannian.ScalarOperators.Extrema.FiniteRegularity
import PoincareLib.Geometry.RicciFlow.Local.Connection.CurvatureIndependence

/-! Compatibility with source names used by the unchanged standard-cap proofs. -/

open scoped Manifold ContDiff

namespace PoincareMT.LeviCivitaData

alias curvatureTensorNorm_eq := localTheory_curvatureTensorNorm_eq

end PoincareMT.LeviCivitaData

namespace PoincareMT.M34.Source

theorem laplacian_nonneg_of_isLocalMin_smoothAt
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) {f : M → ℝ} {q : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f q) (hmin : IsLocalMin f q) :
    0 ≤ D.laplacian f q :=
  D.laplacian_nonneg_of_isLocalMin_contMDiffAt (hf.of_le (by decide)) hmin

end PoincareMT.M34.Source
