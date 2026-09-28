import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceFiniteHessian
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceFiniteChristoffel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff

namespace PoincareConjecture.CoordinateTransition

theorem uniform_finite_derivative_bounds_of_local_isometries
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} {U V : Set E}
    (hU : IsOpen U) (hV : IsOpen V) (hVbounded : Bornology.IsBounded V)
    {A B : ι → E → E →L[ℝ] E →L[ℝ] ℝ} {f : ι → E → E}
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U)
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) V)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U)
    (hBsymm : ∀ i x, x ∈ V → ∀ u v, B i x u v = B i x v u)
    {a : ℝ} (ha : 0 < a)
    (hAlow : ∀ i x, x ∈ U → ∀ v, a * ‖v‖ ^ 2 ≤ A i x v v)
    (hBlow : ∀ i x, x ∈ V → ∀ v, a * ‖v‖ ^ 2 ≤ B i x v v)
    (hAj : HasUniformJetBoundsOn (n + 1) U A)
    (hBj : HasUniformJetBoundsOn (n + 1) V B)
    (hmap : ∀ i, MapsTo (f i) U V)
    (hmetric : ∀ i x, x ∈ U → ∀ u v,
      B i (f i x) (fderiv ℝ (f i) x u) (fderiv ℝ (f i) x v) = A i x u v) :
    HasUniformJetBoundsOn (n + 2) U f := by
  let ΓA := fun i => CoordinateExponential.christoffelBilinear (A i)
  let ΓB := fun i => CoordinateExponential.christoffelBilinear (B i)
  obtain ⟨C0, hC0⟩ := hVbounded.exists_norm_le
  have hzero : ∃ C : ℝ, ∀ i x, x ∈ U → ‖f i x‖ ≤ C :=
    ⟨C0, fun i x hx => hC0 (f i x) (hmap i hx)⟩
  obtain ⟨CA, hCA⟩ := hAj 0 (Nat.zero_le _)
  have hfirst : ∃ C : ℝ, ∀ i x, x ∈ U → ‖fderiv ℝ (f i) x‖ ≤ C := by
    refine ⟨Real.sqrt (max CA 0 / a), fun i x hx => ?_⟩
    apply norm_le_of_pullback_quadratic_bounds (A i x) (B i (f i x))
      (fderiv ℝ (f i) x) ha (le_max_right _ _)
      (fun v => ?_) (hBlow i (f i x) (hmap i hx)) (hmetric i x hx)
    have hnorm : ‖A i x‖ ≤ max CA 0 :=
      (by simpa only [norm_iteratedFDeriv_zero] using hCA i x hx : ‖A i x‖ ≤ CA).trans
        (le_max_left _ _)
    calc
      A i x v v ≤ ‖A i x v v‖ := le_abs_self _
      _ ≤ ‖A i x‖ * (‖v‖ * ‖v‖) := by
        simpa only [mul_assoc] using (A i x).le_opNorm₂ v v
      _ ≤ max CA 0 * (‖v‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_right hnorm (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = max CA 0 * ‖v‖ ^ 2 := by rw [pow_two]
  have hΓA : HasUniformJetBoundsOn n U ΓA :=
    hasUniformJetBoundsOn_christoffelBilinear_finite hU hA hAj ha hAlow
  have hΓB : HasUniformJetBoundsOn n V ΓB :=
    hasUniformJetBoundsOn_christoffelBilinear_finite hV hB hBj ha hBlow
  have hsΓA : ∀ i, ContDiffOn ℝ ∞ (ΓA i) U :=
    fun i => contDiffOn_christoffelBilinear_of_uniformEllipticity hU hA ha hAlow i
  have hsΓB : ∀ i, ContDiffOn ℝ ∞ (ΓB i) V :=
    fun i => contDiffOn_christoffelBilinear_of_uniformEllipticity hV hB ha hBlow i
  apply hasUniformJetBoundsOn_of_finite_christoffel_hessian hU hV hf
    hsΓA hsΓB hmap hΓA hΓB hzero hfirst
  intro i x hx u v
  have hAi := fun y hy => isInvertible_of_uniformEllipticity ha (hAlow i y hy)
  have hBi := fun y hy => isInvertible_of_uniformEllipticity ha (hBlow i y hy)
  have hH := fderiv_fderiv_eq_transitionHessianPolynomial_on hU hV (hA i) (hB i)
    hAi hBi (hBsymm i) (hf i) (hmap i)
    (fun y hy => surjective_of_pullback_isInvertible (hAi y hy)
      (fun v w => (hmetric i y hy v w).symm))
    (fun y hy v w => (hmetric i y hy v w).symm) hx
  simpa [ΓA, ΓB] using congrArg (fun L => L u v) hH

end PoincareConjecture.CoordinateTransition
