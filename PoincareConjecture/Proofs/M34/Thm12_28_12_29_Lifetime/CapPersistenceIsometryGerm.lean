import PoincareConjecture.Proofs.M34.Mathlib.CapPersistenceHessianGerm
import PoincareConjecture.Proofs.M34.Standard.MetricChristoffelGermBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Transition.Hessian
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.TransitionBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_local_isometry_germ_jet_bound (n : ℕ) {a K : ℝ}
    (ha : 0 < a) (hK : 1 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (A B : E → E →L[ℝ] E →L[ℝ] ℝ)
      (f : E → E) (U V : Set E) (x : E),
      IsOpen U → IsOpen V → x ∈ U →
      ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ B V → ContDiffOn ℝ ∞ f U →
      (∀ y ∈ U, (A y).IsInvertible) → (∀ y ∈ V, (B y).IsInvertible) →
      (∀ y ∈ V, ∀ v w, B y v w = B y w v) → MapsTo f U V →
      (∀ y ∈ U, ∀ v w,
        A y v w = B (f y) (fderiv ℝ f y v) (fderiv ℝ f y w)) →
      ‖f x‖ ≤ K →
      (∀ j ≤ n + 1, ‖iteratedFDeriv ℝ j A x‖ ≤ K) →
      (∀ j ≤ n + 1, ‖iteratedFDeriv ℝ j B (f x)‖ ≤ K) →
      (∀ v, a * ‖v‖ ^ 2 ≤ A x v v) →
      (∀ v, a * ‖v‖ ^ 2 ≤ B (f x) v v) →
      ∀ j ≤ n + 2, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  obtain ⟨G, hG, hGb⟩ := exists_christoffel_germ_jet_bound (E := E) n ha hK
  let K1 := max K (max G (Real.sqrt (K / a)))
  have hK1 : 1 ≤ K1 := hK.trans (le_max_left _ _)
  obtain ⟨C, hC, hCb⟩ := exists_finite_hessian_germ_jet_bound
    (E := E) (F := E) n hK1
  refine ⟨C, hC, ?_⟩
  intro A B f U V x hU hV hx hA hB hf hAi hBi hsymm hmap hmetric
    hzero hAj hBj hAlow hBlow
  have hA0 := hA.contDiffAt (hU.mem_nhds hx)
  have hB0 := hB.contDiffAt (hV.mem_nhds (hmap hx))
  have hf0 := hf.contDiffAt (hU.mem_nhds hx)
  have hfirst : ‖fderiv ℝ f x‖ ≤ Real.sqrt (K / a) := by
    apply norm_le_of_pullback_quadratic_bounds (A x) (B (f x)) (fderiv ℝ f x)
      ha (zero_le_one.trans hK) (fun v => ?_) hBlow
      (fun v w => (hmetric x hx v w).symm)
    have hnorm : ‖A x‖ ≤ K := by
      simpa only [norm_iteratedFDeriv_zero] using hAj 0 (Nat.zero_le _)
    calc
      A x v v ≤ ‖A x v v‖ := le_abs_self _
      _ ≤ ‖A x‖ * (‖v‖ * ‖v‖) := by
        simpa only [mul_assoc] using (A x).le_opNorm₂ v v
      _ ≤ K * (‖v‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_right hnorm (by positivity)
      _ = K * ‖v‖ ^ 2 := by rw [pow_two]
  have hΓA := CoordinateExponential.contDiffAt_christoffelBilinear hA0 (hAi x hx)
  have hΓB := CoordinateExponential.contDiffAt_christoffelBilinear
    hB0 (hBi (f x) (hmap hx))
  have hH : ∀ᶠ y in 𝓝 x, ∀ v w,
      fderiv ℝ (fderiv ℝ f) y v w =
        fderiv ℝ f y (CoordinateExponential.christoffelBilinear A y v w) -
          CoordinateExponential.christoffelBilinear B (f y)
            (fderiv ℝ f y v) (fderiv ℝ f y w) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    intro v w
    have he := fderiv_fderiv_eq_transitionHessianPolynomial_on hU hV hA hB
      hAi hBi hsymm hf hmap
      (fun z hz => surjective_of_pullback_isInvertible (hAi z hz) (hmetric z hz))
      hmetric hy
    simpa only [transitionHessianPolynomial_apply] using congrArg (fun L => L v w) he
  apply hCb f (CoordinateExponential.christoffelBilinear A)
    (CoordinateExponential.christoffelBilinear B) x hf0 hΓA hΓB hH
    (hzero.trans (le_max_left _ _))
    (hfirst.trans ((le_max_right _ _).trans (le_max_right _ _)))
  · intro j hj
    exact (hGb A x hA0 hAj hAlow j hj).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · intro j hj
    exact (hGb B (f x) hB0 hBj hBlow j hj).trans
      ((le_max_left _ _).trans (le_max_right _ _))

end PoincareConjecture.CoordinateTransition
