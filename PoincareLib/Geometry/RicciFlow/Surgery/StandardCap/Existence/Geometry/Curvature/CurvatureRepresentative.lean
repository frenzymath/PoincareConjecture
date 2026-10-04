import PoincareLib.Geometry.RicciFlow.Local.Curvature.Calculus.CurvatureHom
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Curvature.Calculus.CurvatureHom
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Curvature.Calculus.CurvatureTrilinear
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Metric.MetricCompactBounds
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Metric.MetricInverse

/-!
# A fixed continuous trilinear representative of actual curvature

The public M03 construction supplies a continuous trilinear map equal to
the retained curvature on every input. Choosing that map gives actual
curvature fields for all chart energies without assuming a representative
as additional data. This serves Morgan-Tian Section 12.5, pp. 309-319.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- Curvature has three nested continuous-linear input slots.
set_option maxSynthPendingDepth 8

open scoped Manifold ContDiff

namespace PoincareMT.M34

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- The continuous trilinear map representing the actual retained curvature
(Section 12.5, pp. 309-319). -/
noncomputable def curvatureTrilinearMap (D : LeviCivitaData g) (x : M) :
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x :=
  Classical.choose (Proofs.M03.exists_curvature_continuousTrilinearMap D x)

/-- The selected representative evaluates to actual curvature with the
frozen order of all three input slots (Section 12.5, pp. 309-319). -/
theorem curvatureTrilinearMap_apply (D : LeviCivitaData g) (x : M)
    (u v w : TangentSpace (𝓡 n) x) :
    curvatureTrilinearMap D x u v w = D.curvature x u v w :=
  Classical.choose_spec (Proofs.M03.exists_curvature_continuousTrilinearMap D x) u v w

end PoincareMT.M34
