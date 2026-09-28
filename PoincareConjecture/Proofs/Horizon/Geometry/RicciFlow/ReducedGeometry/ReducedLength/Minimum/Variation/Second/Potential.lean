import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.CoordinateCurvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Chart
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Scaling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

open ReducedLengthMinimum.Variational ReducedLengthMinimum.Variation.Frame

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem chartActionPotential_hessian {J : Set ℝ} (F : RicciFlow n M J)
    (T s : ℝ) {x y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (ht : T - s ^ 2 ∈ interior J) (v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fderiv ℝ (fun q => chartActionPotential F T x (s, q)))
        (extChartAt (𝓡 n) x y) v w -
      fderiv ℝ (fun q => chartActionPotential F T x (s, q)) (extChartAt (𝓡 n) x y)
        (chartConnection (chartActionMetric F T x) (s, extChartAt (𝓡 n) x y) v w) =
      2 * s ^ 2 * (F.connection (T - s ^ 2)).hessian
        (F.connection (T - s ^ 2)).scalarCurvature y (chartFrame x v y) (chartFrame x w y) := by
  let e := extChartAt (𝓡 n) x
  let D := F.connection (T - s ^ 2)
  let f : M → ℝ := fun z => 2 * s ^ 2 * D.scalarCurvature z
  have hy' : y ∈ e.source := by simpa only [e, extChartAt_source] using hy
  have hq : e y ∈ e.target := e.map_source hy'
  have hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (e.symm (e y)) := by
    rw [e.left_inv hy']
    exact contMDiffAt_const.mul D.contMDiff_scalarCurvature.contMDiffAt
  have h := D.hessian_in_chart x hq hf v w
  dsimp only [e] at h
  rw [← chartFrame_inverse_derivative hy v,
    ← chartFrame_inverse_derivative hy w, (extChartAt (𝓡 n) x).left_inv hy'] at h
  have hpotential : (fun q => chartActionPotential F T x (s, q)) = f ∘ e.symm := rfl
  rw [hpotential, chartConnection_eq_coordinateChristoffel F T s x ht hq]
  rw [← CoordinateExponential.christoffelBilinear_apply, ← h]
  exact D.hessian_const_mul (2 * s ^ 2) D.scalarCurvature y _ _

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
