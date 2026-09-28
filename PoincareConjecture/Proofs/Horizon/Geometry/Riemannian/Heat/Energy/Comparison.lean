import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Energy
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Composition










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [PreconnectedSpace M]
  {g : RiemannianMetric n M}

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M] in
private lemma gradient_const_mul (D : LeviCivitaData g) (c : ℝ) (f : M → ℝ) (x : M) :
    D.gradient (fun y ↦ c * f y) x = c • D.gradient f x := by
  apply (g.inner_isInvertible x).injective
  ext v
  simp only [D.inner_gradient, mvfderiv_const_mul, map_smul, smul_apply, smul_eq_mul]

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M] in
private lemma weighted_comparison_square (D : LeviCivitaData g)
    {η f ξ : M → ℝ} (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hξ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ξ) (x : M) :
    -g.inner x (D.gradient (fun y ↦ 2 * (η y ^ 2 * Real.exp (ξ y) * f y)) x)
        (D.gradient f x) -
      η x ^ 2 * Real.exp (ξ x) * f x ^ 2 *
        g.inner x (D.gradient ξ x) (D.gradient ξ x) ≤
      4 * (Real.exp (ξ x) * f x ^ 2 *
        g.inner x (D.gradient η x) (D.gradient η x)) := by
  have hηd := (hη x).mdifferentiableAt (by simp)
  have hfd := (hf x).mdifferentiableAt (by simp)
  have hξd := (hξ x).mdifferentiableAt (by simp)
  have he : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y ↦ Real.exp (ξ y)) x :=
    (Real.differentiable_exp (ξ x)).mdifferentiableAt.comp x hξd
  have hge : D.gradient (fun y ↦ Real.exp (ξ y)) x =
      Real.exp (ξ x) • D.gradient ξ x := by
    simpa only [Real.deriv_exp, Function.comp_def] using
      D.gradient_comp hξd (Real.differentiable_exp (ξ x))
  have hnonneg (v : TangentSpace (𝓡 n) x) : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  have h₁ := hnonneg (η x • D.gradient f x + (η x * f x) • D.gradient ξ x)
  have h₂ := hnonneg (η x • D.gradient f x + (2 * f x) • D.gradient η x)
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul] at h₁ h₂
  rw [g.symm x (D.gradient ξ x) (D.gradient f x)] at h₁
  rw [g.symm x (D.gradient η x) (D.gradient f x)] at h₂
  have hsq := mul_nonneg (Real.exp_nonneg (ξ x)) (add_nonneg h₁ h₂)
  rw [gradient_const_mul,
    D.gradient_mul (f := fun y ↦ η y ^ 2 * Real.exp (ξ y))
      (((hη.pow 2).mul (Real.contDiff_exp.contMDiff.comp hξ)) x |>.mdifferentiableAt (by simp)) hfd,
    D.gradient_mul (f := fun y ↦ η y ^ 2) (h := fun y ↦ Real.exp (ξ y))
      ((hη.pow 2) x |>.mdifferentiableAt (by simp)) he, hge]
  simp only [pow_two, D.gradient_mul hηd hηd]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  rw [g.symm x (D.gradient η x) (D.gradient f x),
    g.symm x (D.gradient ξ x) (D.gradient f x)]
  nlinarith



theorem weighted_subsolution_spatial_cutoff_estimate (D : LeviCivitaData g)
    {η f ξ d e : M → ℝ}
    (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η) (hηc : HasCompactSupport η)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hξ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ξ)
    (hd : Continuous d) (he : Continuous e)
    (hf0 : ∀ x, 0 ≤ f x) (hsub : ∀ x, d x ≤ D.laplacian f x)
    (hweight : ∀ x, e x + g.inner x (D.gradient ξ x) (D.gradient ξ x) ≤ 0) :
    (∫ x, η x ^ 2 * Real.exp (ξ x) * (2 * f x * d x + f x ^ 2 * e x)
      ∂g.volumeMeasure) ≤
      4 * ∫ x, Real.exp (ξ x) * f x ^ 2 *
        g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure := by
  let ψ : M → ℝ := fun x ↦ 2 * (η x ^ 2 * Real.exp (ξ x) * f x)
  let A : M → ℝ := fun x ↦ η x ^ 2 * Real.exp (ξ x) * f x ^ 2 *
    g.inner x (D.gradient ξ x) (D.gradient ξ x)
  let B : M → ℝ := fun x ↦ Real.exp (ξ x) * f x ^ 2 *
    g.inner x (D.gradient η x) (D.gradient η x)
  have hηsq : HasCompactSupport (fun x ↦ η x ^ 2) := by
    rw [show (fun x ↦ η x ^ 2) = η * η by funext x; simp [pow_two]]
    exact hηc.mul_right (f := η)
  have hψ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ψ :=
    contMDiff_const.mul (((hη.pow 2).mul (Real.contDiff_exp.contMDiff.comp hξ)).mul hf)
  have hψc : HasCompactSupport ψ := ((hηsq.mul_right).mul_right).mul_left
  have hA : Integrable A g.volumeMeasure :=
    (((((hη.pow 2).continuous.mul (Real.continuous_exp.comp hξ.continuous)).mul (hf.pow 2).continuous).mul
      (D.continuous_inner_gradient hξ hξ))).integrable_of_hasCompactSupport
        (((hηsq.mul_right).mul_right).mul_right)
  have hB : Integrable B g.volumeMeasure :=
    (((Real.continuous_exp.comp hξ.continuous).mul (hf.pow 2).continuous).mul
      (D.continuous_inner_gradient hη hη)).integrable_of_hasCompactSupport
        (D.hasCompactSupport_inner_gradient hηc η).mul_left
  have hL : Integrable (fun x ↦ η x ^ 2 * Real.exp (ξ x) *
      (2 * f x * d x + f x ^ 2 * e x)) g.volumeMeasure :=
    (((hη.pow 2).continuous.mul (Real.continuous_exp.comp hξ.continuous)).mul
      (((hf.continuous.const_mul 2).mul hd).add ((hf.pow 2).continuous.mul he))).integrable_of_hasCompactSupport
        ((hηsq.mul_right).mul_right)
  have hΔ := D.integrable_mul_laplacian hψ hf hψc
  have hG := D.integrable_inner_gradient hψ hf hψc
  have hfirst := integral_mono hL (hΔ.sub hA) (fun x ↦ by
    have hu := mul_le_mul_of_nonneg_left (hsub x)
      (mul_nonneg (mul_nonneg (sq_nonneg (η x)) (Real.exp_nonneg (ξ x)))
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hf0 x)))
    have hw := mul_nonneg
      (mul_nonneg (mul_nonneg (sq_nonneg (η x)) (Real.exp_nonneg (ξ x))) (sq_nonneg (f x)))
      (neg_nonneg.mpr (hweight x))
    dsimp only [ψ, A, Pi.sub_apply]
    nlinarith)
  have hsecond := integral_mono (hG.neg.sub hA) (hB.const_mul 4) (fun x ↦ by
    exact D.weighted_comparison_square hη hf hξ x)
  simp only [Pi.sub_apply, Pi.neg_apply] at hfirst hsecond
  rw [integral_sub hΔ hA, D.integral_mul_laplacian hψ hf hψc] at hfirst
  rw [integral_sub (show Integrable (fun x ↦ -g.inner x (D.gradient ψ x)
      (D.gradient f x)) g.volumeMeasure from hG.neg) hA,
    integral_neg, integral_const_mul] at hsecond
  exact hfirst.trans hsecond

end PoincareConjecture.LeviCivitaData
