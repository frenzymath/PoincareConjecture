import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient












set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


theorem gradient_mul (D : LeviCivitaData g) {f h : M → ℝ} {x : M}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    (hh : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) h x) :
    D.gradient (fun y => f y * h y) x =
      f x • D.gradient h x + h x • D.gradient f x := by
  apply (g.inner_isInvertible x).injective
  ext v
  rw [D.inner_gradient, mvfderiv_fun_mul hf hh]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, D.inner_gradient]


theorem hessian_mul (D : LeviCivitaData g) {f h : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ h)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => f y * h y) x u v =
      f x * D.hessian h x u v + h x * D.hessian f x u v +
      mvfderiv (𝓡 n) f x u * mvfderiv (𝓡 n) h x v +
      mvfderiv (𝓡 n) h x u * mvfderiv (𝓡 n) f x v := by
  have hfx := (hf x).mdifferentiableAt (by simp)
  have hhx := (hh x).mdifferentiableAt (by simp)
  have hgf := (D.contMDiffAt_gradient (hf x)).mdifferentiableAt (by simp)
  have hgh := (D.contMDiffAt_gradient (hh x)).mdifferentiableAt (by simp)
  have hfh : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => f y * h y) x :=
    (hf x).smul (hh x)
  have heq : D.gradient (fun y => f y * h y) =
      f • D.gradient h + h • D.gradient f := by
    funext y
    exact D.gradient_mul ((hf y).mdifferentiableAt (by simp))
      ((hh y).mdifferentiableAt (by simp))
  rw [D.hessian_eq_inner_connection_gradient hfh,
    D.hessian_eq_inner_connection_gradient (hf x),
    D.hessian_eq_inner_connection_gradient (hh x), heq,
    D.connection.isCovariantDerivativeOn.add (hfx.smul_section hgh)
      (hhx.smul_section hgf),
    D.connection.isCovariantDerivativeOn.leibniz hgh hfx,
    D.connection.isCovariantDerivativeOn.leibniz hgf hhx]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul, smul_eq_mul,
    D.inner_gradient]
  ring


theorem laplacian_mul (D : LeviCivitaData g) {f h : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ h) (x : M) :
    D.laplacian (fun y => f y * h y) x =
      f x * D.laplacian h x + h x * D.laplacian f x +
      2 * g.inner x (D.gradient f x) (D.gradient h x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hsum : (∑ i, mvfderiv (𝓡 n) f x (b i) * mvfderiv (𝓡 n) h x (b i)) =
      g.inner x (D.gradient f x) (D.gradient h x) := by
    simp_rw [← D.inner_gradient]
    change (∑ i, inner ℝ (D.gradient f x) (b i) *
      inner ℝ (D.gradient h x) (b i)) = inner ℝ (D.gradient f x) (D.gradient h x)
    calc
      _ = ∑ i, inner ℝ (D.gradient f x) (b i) *
          inner ℝ (b i) (D.gradient h x) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [real_inner_comm (b i) (D.gradient h x)]
      _ = _ := b.sum_inner_mul_inner _ _
  have hsum' : (∑ i, mvfderiv (𝓡 n) h x (b i) * mvfderiv (𝓡 n) f x (b i)) =
      g.inner x (D.gradient f x) (D.gradient h x) := by
    simpa only [mul_comm] using hsum
  unfold laplacian
  simp_rw [D.hessian_mul hf hh]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  change f x * (∑ i, D.hessian h x (b i) (b i)) +
      h x * (∑ i, D.hessian f x (b i) (b i)) +
      (∑ i, mvfderiv (𝓡 n) f x (b i) * mvfderiv (𝓡 n) h x (b i)) +
      (∑ i, mvfderiv (𝓡 n) h x (b i) * mvfderiv (𝓡 n) f x (b i)) = _
  rw [hsum, hsum']
  ring


theorem laplacian_sq (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    D.laplacian (fun y => (f y) ^ 2) x =
      2 * f x * D.laplacian f x +
      2 * g.inner x (D.gradient f x) (D.gradient f x) := by
  simpa only [pow_two, two_mul, add_mul] using D.laplacian_mul hf hf x

end PoincareConjecture.LeviCivitaData
