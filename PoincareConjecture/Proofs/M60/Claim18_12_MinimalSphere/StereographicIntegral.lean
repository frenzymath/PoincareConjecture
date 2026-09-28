import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.Integrability
import PoincareConjecture.Proofs.M58.Cor18_28_PolarIntegration
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture

theorem m60SphereParameter_radial_integral :
    (∫ r in Ioi (0 : ℝ), r * (16 / (r ^ 2 + 4) ^ 2)) = 2 := by
  have hd (r : ℝ) : HasDerivAt (fun s : ℝ => -8 / (s ^ 2 + 4))
      (r * (16 / (r ^ 2 + 4) ^ 2)) r := by
    have h := (hasDerivAt_const r (-8 : ℝ)).div
      (((hasDerivAt_id r).pow 2).add_const 4)
      (show r ^ 2 + 4 ≠ 0 by positivity)
    convert! h using 1
    simp only [Pi.pow_apply, id_eq]
    ring
  have hlim : Tendsto (fun r : ℝ => -8 / (r ^ 2 + 4)) atTop (𝓝 0) := by
    have hsq : Tendsto (fun r : ℝ => r ^ 2 + 4) atTop atTop :=
      tendsto_atTop_add_const_right atTop 4 (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp hsq).const_mul (-8 : ℝ)
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := (0 : ℝ)) (fun r _ => hd r)
    (fun r hr => mul_nonneg hr.le (by positivity)) hlim
  norm_num at h
  exact h

theorem m60SphereParameter_factor_integral :
    (∫ z : LoopPlane, 16 / (‖z‖ ^ 2 + 4) ^ 2) = 4 * Real.pi := by
  rw [← Proofs.M58.integral_polar_loopPlane, polarCoord_target]
  calc
    _ = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        (p.1 * (16 / (p.1 ^ 2 + 4) ^ 2)) * (1 : ℝ) := by
      apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      dsimp only
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp.1,
        Proofs.M58.norm_angularPoint, mul_one, mul_one]
    _ = (∫ r in Ioi (0 : ℝ), r * (16 / (r ^ 2 + 4) ^ 2)) *
        (∫ t in Ioo (-Real.pi) Real.pi, (1 : ℝ)) := by
      change (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        (p.1 * (16 / (p.1 ^ 2 + 4) ^ 2)) * (1 : ℝ) ∂volume.prod volume) = _
      exact setIntegral_prod_mul (fun r : ℝ => r * (16 / (r ^ 2 + 4) ^ 2))
        (fun _ : ℝ => 1) (Ioi (0 : ℝ)) (Ioo (-Real.pi) Real.pi)
    _ = 4 * Real.pi := by
      rw [m60SphereParameter_radial_integral]
      simp only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : 0 ≤ Real.pi - -Real.pi),
        smul_eq_mul, mul_one]
      ring

end PoincareConjecture
