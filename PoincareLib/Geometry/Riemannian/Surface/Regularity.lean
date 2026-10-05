import PoincareLib.Geometry.Riemannian.Coordinates.Exponential.JetBounds.ManifoldCurvatureSmooth
import PoincareLib.Geometry.Riemannian.Tensor.Algebra
import PoincareLib.Geometry.Riemannian.Tensor.TraceRegularity

/-!
# Regularity of curvature for surface integration

Metric contraction of the smooth retained curvature tensor gives smooth Ricci
and scalar curvature. The argument works in every dimension and requires no
additional curvature-calculus hypothesis.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Ricci curvature is a smooth tensor for the retained Levi-Civita connection. -/
theorem ricciEvaluation_isSmooth_manifold (D : LeviCivitaData g) :
    IsSmoothCovariantTensor D.ricciEvaluation := by
  let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective ![2, 0, 3, 1] (by decide)
  have h := (D.riemannEvaluation_isSmooth_manifold.perm σ).tensorTrace (g := g)
  convert h using 1
  funext x v
  rfl

/-- The scalar curvature of a smooth Riemannian metric is smooth. -/
theorem contMDiff_scalarCurvature (D : LeviCivitaData g) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ D.scalarCurvature := by
  intro x
  have h := (D.ricciEvaluation_isSmooth_manifold.tensorTrace (g := g)).contMDiffAt_apply
    (x := x) (X := fun i : Fin 0 => Fin.elim0 i) (fun i => Fin.elim0 i)
  convert h using 1
  funext y
  unfold RiemannianMetric.tensorTrace scalarCurvature
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- The retained scalar curvature is continuous. -/
theorem continuous_scalarCurvature (D : LeviCivitaData g) :
    Continuous D.scalarCurvature :=
  D.contMDiff_scalarCurvature.continuous

end PoincareMT.LeviCivitaData
