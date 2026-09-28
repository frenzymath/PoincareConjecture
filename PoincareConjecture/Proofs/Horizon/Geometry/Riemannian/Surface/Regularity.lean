import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.ManifoldCurvatureSmooth
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Algebra
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.TraceRegularity








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


theorem ricciEvaluation_isSmooth_manifold (D : LeviCivitaData g) :
    IsSmoothCovariantTensor D.ricciEvaluation := by
  let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective ![2, 0, 3, 1] (by decide)
  have h := (D.riemannEvaluation_isSmooth_manifold.perm σ).tensorTrace (g := g)
  convert h using 1
  funext x v
  rfl


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


theorem continuous_scalarCurvature (D : LeviCivitaData g) :
    Continuous D.scalarCurvature :=
  D.contMDiff_scalarCurvature.continuous

end PoincareConjecture.LeviCivitaData
