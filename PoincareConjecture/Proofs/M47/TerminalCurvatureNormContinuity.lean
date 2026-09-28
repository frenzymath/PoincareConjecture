import PoincareConjecture.Proofs.M04.CurvatureEnergyBochner
import PoincareConjecture.Proofs.M04.RiemannRegularity
import PoincareConjecture.Proofs.M04.TensorNorm

set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareConjecture.M47

theorem terminalCurvature_norm_continuous
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) :
    Continuous D.curvatureTensorNorm := by
  have hs := (M04.contMDiff_tensorNorm_sq g
    (M04.isSmoothCovariantTensor_riemannEvaluation D)).continuous.sqrt
  convert hs using 1
  funext x
  have hn : g.tensorNorm D.riemannEvaluation x = D.curvatureTensorNorm x :=
    D.curvatureDerivativeNorm_zero x
  rw [hn]
  exact (Real.sqrt_sq (show 0 ≤ D.curvatureTensorNorm x from Real.sqrt_nonneg _)).symm

end PoincareConjecture.M47
