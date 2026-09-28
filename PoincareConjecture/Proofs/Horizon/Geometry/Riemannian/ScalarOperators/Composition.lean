import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.GradientTime
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

omit [IsManifold (𝓡 n) ∞ M] in
private lemma mvfderiv_scalar_comp {f : M → ℝ} {F : ℝ → ℝ} {x : M}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    (hF : DifferentiableAt ℝ F (f x)) (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (F ∘ f) x v = deriv F (f x) * mvfderiv (𝓡 n) f x v := by
  rw [mvfderiv_comp x hF.mdifferentiableAt hf]
  simp only [ContinuousLinearMap.comp_apply, mvfderiv, mfderiv_eq_fderiv]
  rw [hF.hasDerivAt.hasFDerivAt.fderiv]
  change mvfderiv (𝓡 n) f x v * deriv F (f x) =
    deriv F (f x) * mvfderiv (𝓡 n) f x v
  exact mul_comm _ _

theorem gradient_comp (D : LeviCivitaData g) {f : M → ℝ} {F : ℝ → ℝ} {x : M}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    (hF : DifferentiableAt ℝ F (f x)) :
    D.gradient (F ∘ f) x = deriv F (f x) • D.gradient f x := by
  apply (g.inner_isInvertible x).injective
  ext v
  rw [D.inner_gradient, mvfderiv_scalar_comp hf hF]
  simp only [map_smul, smul_apply, smul_eq_mul, D.inner_gradient]

theorem hessian_comp (D : LeviCivitaData g) {f : M → ℝ} {F : ℝ → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hF : ContDiff ℝ ∞ F)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    D.hessian (F ∘ f) x v w =
      deriv F (f x) * D.hessian f x v w +
        deriv (deriv F) (f x) * mvfderiv (𝓡 n) f x v * mvfderiv (𝓡 n) f x w := by
  have hdf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (deriv F ∘ f) :=
    hF.deriv'.contMDiff.comp hf
  have heq : D.gradient (F ∘ f) = (deriv F ∘ f) • D.gradient f := by
    funext y
    exact D.gradient_comp ((hf y).mdifferentiableAt (by simp))
      (hF.differentiable (by simp) (f y))
  rw [D.hessian_eq_inner_connection_gradient ((hF.contMDiff.comp hf) x), heq,
    D.connection.isCovariantDerivativeOn.leibniz
      ((D.contMDiffAt_gradient (hf x)).mdifferentiableAt (by simp))
      ((hdf x).mdifferentiableAt (by simp)),
    D.hessian_eq_inner_connection_gradient (hf x)]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul, smul_eq_mul,
    Function.comp_apply, D.inner_gradient]
  rw [mvfderiv_scalar_comp ((hf x).mdifferentiableAt (by simp))
    ((hF.deriv' (n := ∞)).differentiable (by simp) (f x))]

theorem laplacian_comp (D : LeviCivitaData g) {f : M → ℝ} {F : ℝ → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hF : ContDiff ℝ ∞ F) (x : M) :
    D.laplacian (F ∘ f) x = deriv F (f x) * D.laplacian f x +
      deriv (deriv F) (f x) * g.inner x (D.gradient f x) (D.gradient f x) := by
  unfold laplacian
  simp_rw [D.hessian_comp hf hF]
  simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  rw [D.sum_mvfderiv_mul_eq_inner_gradient]

end PoincareConjecture.LeviCivitaData
