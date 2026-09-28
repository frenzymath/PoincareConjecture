import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Calculus
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.TraceRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture

lemma LeviCivitaData.CurvatureTensorCalculus.contMDiff_scalarCurvature
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} {D : LeviCivitaData g}
    (hD : D.CurvatureTensorCalculus) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ D.scalarCurvature := by
  intro x
  have h := (hD.2.1.tensorTrace (g := g)).contMDiffAt_apply
    (x := x) (X := fun i : Fin 0 => Fin.elim0 i) (fun i => Fin.elim0 i)
  convert h using 1
  funext y
  unfold RiemannianMetric.tensorTrace LeviCivitaData.scalarCurvature
  apply Finset.sum_congr rfl
  intro i _
  rfl

end PoincareConjecture
