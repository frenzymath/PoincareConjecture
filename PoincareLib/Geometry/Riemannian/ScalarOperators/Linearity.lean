import PoincareLib.Geometry.Riemannian.ScalarOperators.Gradient
import PoincareLib.Geometry.Riemannian.ScalarOperators.Scaling

/-! # Additivity of the retained scalar differential operators

Metric duality and connection additivity give the linearity needed when a
scalar heat solution is perturbed by a smooth exhaustion barrier.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- The gradient is additive at differentiability points. -/
lemma gradient_add (D : LeviCivitaData g) {f h : M → ℝ} {x : M}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    (hh : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) h x) :
    D.gradient (fun y => f y + h y) x = D.gradient f x + D.gradient h x := by
  apply (g.inner_isInvertible x).injective
  ext v
  rw [D.inner_gradient, mvfderiv_fun_add hf hh]
  simp only [map_add, add_apply, D.inner_gradient]

/-- Additivity of the Hessian on smooth scalar functions. -/
lemma hessian_add (D : LeviCivitaData g) {f h : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ h)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => f y + h y) x u v =
      D.hessian f x u v + D.hessian h x u v := by
  have heq : D.gradient (fun y => f y + h y) = D.gradient f + D.gradient h := by
    funext y
    exact D.gradient_add ((hf y).mdifferentiableAt (by simp))
      ((hh y).mdifferentiableAt (by simp))
  have hfh : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => f y + h y) x :=
    (hf x).add (hh x)
  rw [D.hessian_eq_inner_connection_gradient hfh,
    D.hessian_eq_inner_connection_gradient (hf x),
    D.hessian_eq_inner_connection_gradient (hh x), heq,
    D.connection.isCovariantDerivativeOn.add
      ((D.contMDiffAt_gradient (hf x)).mdifferentiableAt (by simp))
      ((D.contMDiffAt_gradient (hh x)).mdifferentiableAt (by simp))]
  simp only [add_apply, map_add]

/-- Taking the metric trace preserves scalar additivity. -/
lemma laplacian_add (D : LeviCivitaData g) {f h : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ h) (x : M) :
    D.laplacian (fun y => f y + h y) x = D.laplacian f x + D.laplacian h x := by
  simp only [laplacian, D.hessian_add hf hh, Finset.sum_add_distrib]

/-- Subtraction of a smooth scalar perturbation commutes with the Laplacian. -/
lemma laplacian_sub (D : LeviCivitaData g) {f h : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ h) (x : M) :
    D.laplacian (fun y => f y - h y) x = D.laplacian f x - D.laplacian h x := by
  have heq : (fun y => f y - h y) = (fun y => f y + (-1) * h y) := by
    funext y; ring
  have hneg : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => (-1 : ℝ) * h y) := by
    simpa using hh.neg
  rw [heq, D.laplacian_add hf hneg, D.laplacian_const_mul]
  ring

end PoincareMT.LeviCivitaData
