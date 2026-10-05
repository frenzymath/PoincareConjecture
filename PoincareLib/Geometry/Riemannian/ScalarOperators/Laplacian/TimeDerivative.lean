import PoincareLib.Geometry.Riemannian.ScalarOperators
import PoincareLib.Geometry.Manifold.ContDiff.TimeDerivative
import PoincareLib.Geometry.Manifold.ContDiff.SpatialDerivative

/-!
# Time differentiation of the retained Hessian and Laplacian

For a fixed metric and connection, time differentiation commutes with the
scalar Hessian and its metric trace. The proof differentiates the defining
directional derivatives, so it needs no coordinate formula for the operator.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- The fixed connection's scalar Hessian commutes with time differentiation. -/
theorem hasDerivAt_hessian_of_time_derivative (D : LeviCivitaData g)
    {F : ℝ × M → ℝ} {dF : M → ℝ} {t : ℝ}
    (hF : ∀ x, ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (t, x))
    (hdF : ∀ x, HasDerivAt (fun s => F (s, x)) (dF x) t)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    HasDerivAt (fun s => D.hessian (fun y => F (s, y)) x v w)
      (D.hessian dF x v w) t := by
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w
  have hY := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n))
    (k := ∞) w
  have hG := Poincare.Manifold.contMDiffAt_mvfderiv_spatial (hF x) hY
  have hdG := Poincare.Manifold.hasDerivAt_mvfderiv_time hG
    (fun y => Poincare.Manifold.hasDerivAt_mvfderiv_time (hF y) hdF (Y y)) (X x)
  have hC := Poincare.Manifold.hasDerivAt_mvfderiv_time (hF x) hdF
    (D.connection Y x (X x))
  exact hdG.sub hC

/-- Taking the fixed metric trace commutes with time differentiation. -/
theorem hasDerivAt_laplacian_of_time_derivative (D : LeviCivitaData g)
    {F : ℝ × M → ℝ} {dF : M → ℝ} {t : ℝ}
    (hF : ∀ x, ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (t, x))
    (hdF : ∀ x, HasDerivAt (fun s => F (s, x)) (dF x) t) (x : M) :
    HasDerivAt (fun s => D.laplacian (fun y => F (s, y)) x)
      (D.laplacian dF x) t := by
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    D.hasDerivAt_hessian_of_time_derivative hF hdF x
      (g.orthonormalBasis x i) (g.orthonormalBasis x i))

end PoincareMT.LeviCivitaData
