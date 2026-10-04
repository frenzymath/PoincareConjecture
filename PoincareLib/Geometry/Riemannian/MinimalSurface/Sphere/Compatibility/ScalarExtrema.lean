import PoincareLib.Geometry.RicciFlow.Curvature.Estimates.ScalarTrace

open scoped Manifold ContDiff

namespace PoincareMT.M60

abbrev LeviCivitaData := @PoincareMT.LeviCivitaData

theorem LeviCivitaData.laplacian_nonneg_of_isLocalMin
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x) (hm : IsLocalMin f x) :
    0 ≤ D.laplacian f x :=
  PoincareMT.LeviCivitaData.laplacian_nonneg_of_isLocalMinAt D hf hm

end PoincareMT.M60
