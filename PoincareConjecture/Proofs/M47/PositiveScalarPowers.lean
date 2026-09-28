import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Composition
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv










set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M47Positive

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

omit [IsManifold (𝓡 n) ∞ M] in


theorem contMDiff_positive_rpow {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x) (p : ℝ) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => f x ^ p) := by
  intro x
  exact (Real.contDiffAt_rpow_const_of_ne (hpos x).ne').contMDiffAt.comp x (hf x)



theorem gradient_positive_rpow (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (p : ℝ) (x : M) :
    D.gradient (fun y => f y ^ p) x = (p * f x ^ (p - 1)) • D.gradient f x := by
  simpa only [Function.comp_def, Real.deriv_rpow_const] using
    D.gradient_comp ((hf x).mdifferentiableAt (by simp))
      (Real.hasDerivAt_rpow_const (p := p) (Or.inl (hpos x).ne')).differentiableAt

private theorem mvfderiv_positive_rpow (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (p : ℝ) (x : M) (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y => f y ^ p) x v =
      p * f x ^ (p - 1) * mvfderiv (𝓡 n) f x v := by
  rw [← D.inner_gradient, gradient_positive_rpow D hf hpos p]
  simp only [map_smul, smul_apply, smul_eq_mul, D.inner_gradient]



theorem hessian_positive_rpow (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (p : ℝ) (x : M) (v w : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => f y ^ p) x v w =
      (p * f x ^ (p - 1)) * D.hessian f x v w +
        p * (p - 1) * f x ^ (p - 2) *
          mvfderiv (𝓡 n) f x v * mvfderiv (𝓡 n) f x w := by
  have hpower := contMDiff_positive_rpow hf hpos p
  have hprev := contMDiff_positive_rpow hf hpos (p - 1)
  have hcoef : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => p * f y ^ (p - 1)) := by
    have hc : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun _ : M => p) := contMDiff_const
    exact hc.smul hprev
  have heq : D.gradient (fun y => f y ^ p) =
      (fun y => p * f y ^ (p - 1)) • D.gradient f := by
    funext y
    exact gradient_positive_rpow D hf hpos p y
  have hderiv : mvfderiv (𝓡 n) (fun y => p * f y ^ (p - 1)) x v =
      p * (p - 1) * f x ^ (p - 2) * mvfderiv (𝓡 n) f x v := by
    rw [mvfderiv_fun_mul mdifferentiableAt_const ((hprev x).mdifferentiableAt (by simp))]
    simp only [mvfderiv_const, smul_zero, add_zero, smul_apply, smul_eq_mul]
    rw [mvfderiv_positive_rpow D hf hpos (p - 1)]
    rw [show p - 1 - 1 = p - 2 by ring]
    ring
  rw [D.hessian_eq_inner_connection_gradient (hpower x), heq,
    D.connection.isCovariantDerivativeOn.leibniz
      ((D.contMDiffAt_gradient (hf x)).mdifferentiableAt (by simp))
      ((hcoef x).mdifferentiableAt (by simp)),
    D.hessian_eq_inner_connection_gradient (hf x)]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, smul_eq_mul, D.inner_gradient, hderiv]



theorem laplacian_positive_rpow (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (p : ℝ) (x : M) :
    D.laplacian (fun y => f y ^ p) x =
      (p * f x ^ (p - 1)) * D.laplacian f x +
        p * (p - 1) * f x ^ (p - 2) *
          g.inner x (D.gradient f x) (D.gradient f x) := by
  unfold LeviCivitaData.laplacian
  simp_rw [hessian_positive_rpow D hf hpos]
  simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  rw [D.sum_mvfderiv_mul_eq_inner_gradient]

end PoincareConjecture.M47Positive
