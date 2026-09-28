import PoincareConjecture.Proofs.M28.Mathlib.FiniteHessian.MetricJets
import PoincareConjecture.Proofs.M28.Mathlib.FiniteHessian.Estimate
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.TransitionBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.Proofs.M28.FiniteHessian

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem hasUniformJetBoundsAt_fderiv_of_metric_pullback
    (n : ℕ) {f : ι → E → E} {x : ι → E} {U : ι → Set E}
    {A B : ι → E → E →L[ℝ] E →L[ℝ] ℝ}
    (hU : ∀ i, IsOpen (U i)) (hx : ∀ i, x i ∈ U i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) (U i))
    (hB : ∀ i y, y ∈ U i → ContDiffAt ℝ ∞ (B i) (f i y))
    (hAi : ∀ i y, y ∈ U i → (A i y).IsInvertible)
    (hBi : ∀ i y, y ∈ U i → (B i (f i y)).IsInvertible)
    (hBs : ∀ i y, y ∈ U i → ∀ v w, B i (f i y) v w = B i (f i y) w v)
    (hmetric : ∀ i y, y ∈ U i → ∀ v w,
      A i y v w = B i (f i y) (fderiv ℝ (f i) y v) (fderiv ℝ (f i) y w))
    (hAj : HasUniformJetBoundsAt (n + 1) A x)
    (hBj : HasUniformJetBoundsAt (n + 1) B (fun i => f i (x i)))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hAe : ∀ i v, a * ‖v‖ ^ 2 ≤ A i (x i) v v)
    (hBe : ∀ i v, b * ‖v‖ ^ 2 ≤ B i (f i (x i)) v v) :
    HasUniformJetBoundsAt (n + 1) (fun i => fderiv ℝ (f i)) x := by
  have hf₀ := fun i => (hf i).contDiffAt ((hU i).mem_nhds (hx i))
  have hA₀ := fun i => (hA i).contDiffAt ((hU i).mem_nhds (hx i))
  have hB₀ := fun i => hB i (x i) (hx i)
  have hGammaA := fun i => CoordinateExponential.contDiffAt_christoffelBilinear
    (hA₀ i) (hAi i (x i) (hx i))
  have hGammaB := fun i => CoordinateExponential.contDiffAt_christoffelBilinear
    (hB₀ i) (hBi i (x i) (hx i))
  have hGammaAj := hasUniformJetBoundsAt_christoffelBilinear hAj hA₀ ha hAe
  have hGammaBj := hasUniformJetBoundsAt_christoffelBilinear hBj hB₀ hb hBe
  obtain ⟨C, hC0, hC⟩ := hAj.bound_all
  have hfirst : ∃ K : ℝ, ∀ i, ‖fderiv ℝ (f i) (x i)‖ ≤ K := by
    refine ⟨Real.sqrt (C / b), fun i => ?_⟩
    apply CoordinateTransition.norm_le_of_pullback_quadratic_bounds
      (A i (x i)) (B i (f i (x i))) (fderiv ℝ (f i) (x i)) hb hC0
    · intro v
      have hnorm : ‖A i (x i)‖ ≤ C := by
        simpa only [norm_iteratedFDeriv_zero] using hC 0 (Nat.zero_le _) i
      calc
        A i (x i) v v ≤ ‖A i (x i) v v‖ := le_abs_self _
        _ ≤ ‖A i (x i)‖ * ‖v‖ * ‖v‖ := (A i (x i)).le_opNorm₂ v v
        _ ≤ C * ‖v‖ ^ 2 := by
          nlinarith [mul_le_mul_of_nonneg_right hnorm (sq_nonneg ‖v‖)]
    · exact hBe i
    · exact fun v w => (hmetric i (x i) (hx i) v w).symm
  apply hasUniformJetBoundsAt_fderiv_of_hessian n hf₀ hGammaA hGammaB
    hGammaAj hGammaBj hfirst
  intro i
  filter_upwards [(hU i).mem_nhds (hx i)] with y hy
  have hmetric_germ : ∀ᶠ z in 𝓝 y, ∀ v w,
      A i z v w = B i (f i z) (fderiv ℝ (f i) z v) (fderiv ℝ (f i) z w) := by
    filter_upwards [(hU i).mem_nhds hy] with z hz
    exact hmetric i z hz
  have hsurj := CoordinateTransition.surjective_of_pullback_isInvertible
    (hAi i y hy) (hmetric i y hy)
  intro v w
  exact (CoordinateTransition.transitionHessianPolynomial_eq
    (((hA i).contDiffAt ((hU i).mem_nhds hy)).differentiableAt (by simp))
    ((hB i y hy).differentiableAt (by simp)) (hAi i y hy) (hBi i y hy)
    (hBs i y hy) ((hf i).contDiffAt ((hU i).mem_nhds hy)) hsurj
    hmetric_germ v w).symm

end PoincareConjecture.Proofs.M28.FiniteHessian
