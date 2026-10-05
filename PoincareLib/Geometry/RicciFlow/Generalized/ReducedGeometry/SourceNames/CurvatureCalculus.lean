import PoincareLib.Geometry.Riemannian.Curvature.IntrinsicCalculus

/-! Source name for the existing retained-connection curvature calculus. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

theorem LeviCivitaData.normalization_curvatureTensorCalculus
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) :
    D.CurvatureTensorCalculus := D.intrinsicCurvatureTensorCalculus

end PoincareMT
