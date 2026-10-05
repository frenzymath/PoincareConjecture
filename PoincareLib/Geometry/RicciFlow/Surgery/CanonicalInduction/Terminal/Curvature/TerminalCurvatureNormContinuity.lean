import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.SourceNames
import PoincareLib.Geometry.RicciFlow.Curvature.Energy.Bochner
import PoincareLib.Geometry.RicciFlow.Curvature.Calculus.Tensors.RiemannRegularity
import PoincareLib.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorPullback

/-!
# Continuity of the actual static full curvature norm

The smooth squared tensor norm and its nonnegative square root give
continuity, including at flat points.
Source: derivations/terminal-curvature-parallel-flow.md, Stage C6d.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareMT.M47

/-- The actual full curvature norm of a smooth metric is continuous. -/
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

end PoincareMT.M47
