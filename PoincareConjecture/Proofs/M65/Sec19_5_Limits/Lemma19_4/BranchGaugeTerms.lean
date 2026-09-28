import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchCauchyDerivative











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Metric
open scoped Topology ContDiff

namespace PoincareConjecture.M65Branch

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B]



def cauchyTerm (A : ℂ → B) : ℕ → ℂ → B
  | 0 => fun _ => 1
  | n + 1 => cauchyOperator (fun z => A z * cauchyTerm A n z)



theorem contDiff_cauchyTerm {A : ℂ → B} (hA : ContDiff ℝ 1 A)
    (hs : HasCompactSupport A) (n : ℕ) : ContDiff ℝ 1 (cauchyTerm A n) := by
  induction n with
  | zero => exact contDiff_const
  | succ n ih => exact contDiff_cauchyOperator (hA.mul ih) hs.mul_right

variable [CompleteSpace B]




theorem dbar_cauchyTerm_succ {A : ℂ → B} (hA : ContDiff ℝ 1 A)
    (hs : HasCompactSupport A) (n : ℕ) (z : ℂ) :
    dbar (cauchyTerm A (n + 1)) z = A z * cauchyTerm A n z :=
  dbar_cauchyOperator (hA.mul (contDiff_cauchyTerm hA hs n)) hs.mul_right z





theorem cauchyTerm_bounds [NormOneClass B] {A : ℂ → B} {R B0 B1 δ : ℝ}
    (hR : 0 < R) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hδ : 0 < δ)
    (hA : ContDiff ℝ 1 A) (hsupport : tsupport A ⊆ closedBall (0 : ℂ) R)
    (hvalue : ∀ z, ‖A z‖ ≤ B0) (hderiv : ∀ z, ‖fderiv ℝ A z‖ ≤ B1)
    (n : ℕ) (z : ℂ) :
    ‖cauchyTerm A n z‖ ≤ (8 * R * (B0 + δ * B1)) ^ n ∧
      ‖fderiv ℝ (cauchyTerm A n) z‖ ≤ δ⁻¹ * (8 * R * (B0 + δ * B1)) ^ n := by
  let q := 8 * R * (B0 + δ * B1)
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hs : HasCompactSupport A :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset isClosed_closure hsupport
  change ‖cauchyTerm A n z‖ ≤ q ^ n ∧ ‖fderiv ℝ (cauchyTerm A n) z‖ ≤ δ⁻¹ * q ^ n
  induction n generalizing z with
  | zero =>
    constructor
    · simp only [cauchyTerm, norm_one, pow_zero, le_refl]
    · change ‖fderiv ℝ (fun _ : ℂ => (1 : B)) z‖ ≤ δ⁻¹ * q ^ 0
      rw [(hasFDerivAt_const (𝕜 := ℝ) (1 : B) z).fderiv, norm_zero, pow_zero, mul_one]
      exact inv_nonneg.mpr hδ.le
  | succ n ih =>
    have hT := contDiff_cauchyTerm hA hs n
    have hprod : ContDiff ℝ 1 (fun w => A w * cauchyTerm A n w) := hA.mul hT
    have hprodSupport : tsupport (fun w => A w * cauchyTerm A n w) ⊆
        closedBall (0 : ℂ) R := (tsupport_mul_subset_left).trans hsupport
    have hprodValue (w : ℂ) : ‖A w * cauchyTerm A n w‖ ≤ B0 * q ^ n :=
      (norm_mul_le _ _).trans (mul_le_mul (hvalue w) (ih w).1 (norm_nonneg _) hB0)
    have hprodDeriv (w : ℂ) :
        ‖fderiv ℝ (fun y => A y * cauchyTerm A n y) w‖ ≤
          (B0 * δ⁻¹ + B1) * q ^ n := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro v
      rw [fderiv_fun_mul' (hA.differentiable one_ne_zero w) (hT.differentiable one_ne_zero w)]
      change ‖A w * fderiv ℝ (cauchyTerm A n) w v +
        fderiv ℝ A w v * cauchyTerm A n w‖ ≤ _
      have hDv : ‖fderiv ℝ (cauchyTerm A n) w v‖ ≤ (δ⁻¹ * q ^ n) * ‖v‖ :=
        ((fderiv ℝ (cauchyTerm A n) w).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (ih w).2 (norm_nonneg v))
      have hAv : ‖fderiv ℝ A w v‖ ≤ B1 * ‖v‖ :=
        ((fderiv ℝ A w).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (hderiv w) (norm_nonneg v))
      calc
        _ ≤ ‖A w‖ * ‖fderiv ℝ (cauchyTerm A n) w v‖ +
            ‖fderiv ℝ A w v‖ * ‖cauchyTerm A n w‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
        _ ≤ B0 * ((δ⁻¹ * q ^ n) * ‖v‖) + (B1 * ‖v‖) * q ^ n :=
          add_le_add (mul_le_mul (hvalue w) hDv (norm_nonneg _) hB0)
            (mul_le_mul hAv (ih w).1 (norm_nonneg _) (by positivity))
        _ = _ := by ring
    constructor
    · change ‖cauchyOperator (fun w => A w * cauchyTerm A n w) z‖ ≤ _
      apply (norm_cauchyOperator_le hR (by positivity) hprod.continuous
        ((subset_tsupport _).trans hprodSupport) (fun w _ => hprodValue w) z).trans
      have hco : 8 * R * B0 ≤ q :=
        mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (mul_nonneg hδ.le hB1)) (by positivity)
      calc
        _ = (8 * R * B0) * q ^ n := by ring
        _ ≤ q * q ^ n := mul_le_mul_of_nonneg_right hco (pow_nonneg hq n)
        _ = _ := by rw [pow_succ]; ring
    · change ‖fderiv ℝ (cauchyOperator (fun w => A w * cauchyTerm A n w)) z‖ ≤ _
      apply (norm_fderiv_cauchyOperator_le hR (by positivity) hprod
        hprodSupport (fun w _ => hprodDeriv w) z).trans_eq
      rw [pow_succ]
      dsimp only [q]
      field_simp

end PoincareConjecture.M65Branch
