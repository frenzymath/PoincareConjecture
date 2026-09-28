import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchCauchyWeakDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Complex
open scoped Topology SchwartzMap ContDiff

namespace PoincareConjecture.M65Branch

theorem cauchyOperator_weak_dbar_C1 {h : ℂ → ℂ} {R B : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B) (hh : MemLp h 2 volume)
    (hs : Function.support h ⊆ Metric.closedBall (0 : ℂ) R)
    (hb : ∀ z, ‖h z‖ ≤ B) (φ : ℂ → ℂ)
    (hφd : ContDiff ℝ 1 φ) (hφ : HasCompactSupport φ) :
    (∫ z, dbar φ z * cauchyOperator h z) = -∫ z, φ z * h z := by
  let u := hh.toLp h
  let D0 := u + beurlingL2 u
  let D1 := I • (beurlingL2 u - u)
  have h0 : (∫ z, φ z * D0 z) = -∫ z, fderiv ℝ φ z 1 * cauchyOperator h z :=
    (cauchyOperator_weak_derivatives_C1 hR hB hh hs hb φ hφd hφ).1
  have h1 : (∫ z, φ z * D1 z) = -∫ z, fderiv ℝ φ z I * cauchyOperator h z :=
    (cauchyOperator_weak_derivatives_C1 hR hB hh hs hb φ hφd hφ).2
  have hφL2 : MemLp φ 2 volume := hφd.continuous.memLp_of_hasCompactSupport hφ
  have hi0 : Integrable (fun z => φ z * D0 z) :=
    hφL2.integrable_mul (Lp.memLp D0)
  have hi1 : Integrable (fun z => φ z * D1 z) :=
    hφL2.integrable_mul (Lp.memLp D1)
  have hCi := continuous_cauchyOperator_of_bound hB hh.1 hs hb
  have hit (v : ℂ) : Integrable (fun z => fderiv ℝ φ z v * cauchyOperator h z) := by
    have hD : Continuous (fun z => fderiv ℝ φ z v) :=
      (hφd.continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact (hD.mul hCi).integrable_of_hasCompactSupport (hφ.fderiv_apply ℝ v).mul_right
  have hsum : (∫ z, φ z * D0 z) + I * (∫ z, φ z * D1 z) =
      2 * ∫ z, φ z * h z := by
    rw [← integral_const_mul, ← integral_add hi0 (hi1.const_mul I), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add u (beurlingL2 u),
      Lp.coeFn_smul I (beurlingL2 u - u), Lp.coeFn_sub (beurlingL2 u) u,
      hh.coeFn_toLp] with z ha hm hs hu
    dsimp only [D0, D1]
    rw [ha, hm, Pi.add_apply, Pi.smul_apply, hs, Pi.sub_apply, smul_eq_mul]
    change φ z * (u z + beurlingL2 u z) + I * (φ z * (I * (beurlingL2 u z - u z))) = _
    have hI := I_mul_I
    have huz : u z = h z := hu
    rw [huz]
    linear_combination (φ z * (beurlingL2 u z - h z)) * hI
  calc
    _ = (2 : ℂ)⁻¹ * ((∫ z, fderiv ℝ φ z 1 * cauchyOperator h z) +
        I * ∫ z, fderiv ℝ φ z I * cauchyOperator h z) := by
      simp only [dbar, dbarLinear, smul_apply, add_apply, ContinuousLinearMap.apply_apply,
        smul_eq_mul]
      simp_rw [mul_assoc, add_mul, mul_assoc]
      rw [integral_const_mul, integral_add (hit 1) ((hit I).const_mul I), integral_const_mul]
    _ = -(2 : ℂ)⁻¹ * ((∫ z, φ z * D0 z) + I * ∫ z, φ z * D1 z) := by
      rw [h0, h1]
      ring
    _ = _ := by rw [hsum]; ring

theorem cauchyOperator_weak_dbar {h : ℂ → ℂ} {R B : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B) (hh : MemLp h 2 volume)
    (hs : Function.support h ⊆ Metric.closedBall (0 : ℂ) R)
    (hb : ∀ z, ‖h z‖ ≤ B) (φ : 𝓢(ℂ, ℂ))
    (hφ : HasCompactSupport (φ : ℂ → ℂ)) :
    (∫ z, dbar φ z * cauchyOperator h z) = -∫ z, φ z * h z :=
  cauchyOperator_weak_dbar_C1 hR hB hh hs hb φ (φ.smooth 1) hφ

end PoincareConjecture.M65Branch
