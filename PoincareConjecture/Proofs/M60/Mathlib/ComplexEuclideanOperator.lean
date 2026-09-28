import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.M60

noncomputable def complexCoordinates (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i)

theorem complexCoordinates_apply {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    complexCoordinates n v i = (v i : ℂ) := rfl

noncomputable def complexifyEuclideanOperator (n : ℕ) :
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ]
      ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun L => ContinuousLinearMap.pi fun i =>
        ∑ j : Fin n, (L (EuclideanSpace.basisFun (Fin n) ℝ j) i : ℂ) •
          ContinuousLinearMap.proj j
      map_add' := by
        intro L K
        ext v i
        simp [Finset.sum_add_distrib, add_mul]
      map_smul' := by
        intro r L
        ext v i
        simp [Complex.real_smul, Finset.mul_sum, mul_assoc] }

theorem complexifyEuclideanOperator_apply {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : Fin n → ℂ) (i : Fin n) :
    complexifyEuclideanOperator n L v i =
      ∑ j : Fin n, (L (EuclideanSpace.basisFun (Fin n) ℝ j) i : ℂ) * v j := by
  simp [complexifyEuclideanOperator]

theorem complexifyEuclideanOperator_real {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) :
    complexifyEuclideanOperator n L (complexCoordinates n v) =
      complexCoordinates n (L v) := by
  have hb : (∑ j : Fin n, v j • EuclideanSpace.basisFun (Fin n) ℝ j) = v :=
    (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  ext i
  rw [complexifyEuclideanOperator_apply, complexCoordinates_apply]
  simp only [complexCoordinates_apply]
  calc
    _ = ((∑ j : Fin n, v j * L (EuclideanSpace.basisFun (Fin n) ℝ j) i : ℝ) : ℂ) := by
      simp only [Complex.ofReal_sum, Complex.ofReal_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (L (∑ j : Fin n, v j • EuclideanSpace.basisFun (Fin n) ℝ j) i : ℂ) := by
      simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply,
        PiLp.smul_apply, smul_eq_mul]
    _ = _ := by rw [hb]

theorem complexCoordinates_sub_I_smul_eq_zero_iff {n : ℕ}
    (a b : EuclideanSpace ℝ (Fin n)) :
    complexCoordinates n a - Complex.I • complexCoordinates n b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have he (i : Fin n) := congrFun h i
    constructor
    · ext i
      change a i = 0
      have hr := congrArg Complex.re (he i)
      simpa only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, complexCoordinates_apply,
        smul_eq_mul, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Complex.zero_re]
        using hr
    · ext i
      change b i = 0
      have hi := congrArg Complex.im (he i)
      simpa only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, complexCoordinates_apply,
        smul_eq_mul, Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add, zero_sub,
        Complex.zero_im, neg_eq_zero] using hi
  · rintro ⟨rfl, rfl⟩
    simp

end PoincareConjecture.M60
