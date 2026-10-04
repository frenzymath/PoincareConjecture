import PoincareLib.Geometry.RicciFlow.Curvature.Energy.Regularity
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Fields.ConnectionScalar
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Fields.FixedExtension
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Identities.CurvatureAlgebra
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Identities.CurvatureSymmetries
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Tensors.RicciRegularity
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Tensors.RiemannRegularity
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Tensors.TensorDerivativeClosure
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Energy.Regularity
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Estimates.QuadraticRicci

/-!
# Continuity of all intrinsic curvature derivative norms

The actual squared tensor norms are jointly smooth within the flow
domain. Their nonnegative square roots give joint continuity, including
time endpoints. This passes the bounds to the terminal slice in
Morgan-Tian Theorem 12.5, pp. 296-297.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.RicciFlow

/-- Every actual covariant curvature derivative norm is jointly
continuous on the included flow domain (Theorem 12.5, pp. 296-297). -/
theorem continuousOn_curvatureDerivativeNorm
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (F : RicciFlow n M J) (m : ℕ) :
    ContinuousOn (fun p : ℝ × M => (F.connection p.1).curvatureDerivativeNorm m p.2)
      (J ×ˢ univ) := by
  have hsq := (M04.contMDiffOn_flow_curvatureDerivativeEnergy F m).continuousOn
  apply hsq.sqrt.congr
  intro p _hp
  change (F.connection p.1).curvatureDerivativeNorm m p.2 =
    Real.sqrt (((F.connection p.1).curvatureDerivativeNorm m p.2) ^ 2)
  rw [Real.sqrt_sq_eq_abs]
  exact (abs_of_nonneg (Real.sqrt_nonneg _)).symm

end PoincareMT.RicciFlow
