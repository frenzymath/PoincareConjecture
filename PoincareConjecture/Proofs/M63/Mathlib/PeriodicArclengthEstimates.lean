import PoincareConjecture.Proofs.M63.Mathlib.PeriodicArclength
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff

namespace PoincareConjecture.M63

theorem exists_smooth_periodic_arclength_homeomorph_estimates {L : ℝ}
    (hL : 0 < L) {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (hperiod : Function.Periodic v L) (hpos : ∀ x, 0 < v x)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hvnear : ∀ x, |v x - 1| ≤ δ) (hvderiv : ∀ x, |deriv v x| ≤ δ) :
    let ell := ∫ x in (0 : ℝ)..L, v x
    let m := ell / L
    0 < ell ∧ |m - 1| ≤ δ ∧ ∃ phi : ℝ ≃ₜ ℝ,
      (∀ x, phi x = (L / ell) * ∫ y in (0 : ℝ)..x, v y) ∧
      ContDiff ℝ ∞ (phi : ℝ → ℝ) ∧ ContDiff ℝ ∞ (phi.symm : ℝ → ℝ) ∧
      phi 0 = 0 ∧ (∀ x, phi (x + L) = phi x + L) ∧
      (∀ x, phi.symm (x + L) = phi.symm x + L) ∧
      (∀ x, HasDerivAt phi (v x / m) x) ∧
      (∀ x, HasDerivAt (deriv phi) (deriv v x / m) x) ∧
      (∀ x, HasDerivAt phi.symm (m / v (phi.symm x)) x) ∧
      (∀ x, HasDerivAt (deriv phi.symm)
        (-(m ^ 2 * deriv v (phi.symm x)) / v (phi.symm x) ^ 3) x) ∧
      (∀ x, 0 < deriv phi x ∧ 0 < deriv phi.symm x) ∧
      (∀ x, |phi x - x| ≤ 4 * L * δ) ∧
      (∀ x, |deriv phi x - 1| ≤ 4 * δ) ∧
      (∀ x, |deriv (deriv phi) x| ≤ 2 * δ) ∧
      (∀ x, |phi.symm x - x| ≤ 4 * L * δ) ∧
      (∀ x, |deriv phi.symm x - 1| ≤ 4 * δ) ∧
      ∀ x, |deriv (deriv phi.symm) x| ≤ 18 * δ := by
  let ell := ∫ x in (0 : ℝ)..L, v x
  let m := ell / L
  obtain ⟨hell, phi, hformula, hphi, _hpsi, hzero, hshift, hinvshift, hd, hid⟩ :=
    exists_periodic_arclength_homeomorph hL (hv.of_le (by simp)) hperiod hpos
  have hmpos : 0 < m := div_pos hell hL
  have hellnear : |ell - L| ≤ δ * L := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := L) (fun x _ => show ‖v x - 1‖ ≤ δ from hvnear x)
    rw [intervalIntegral.integral_sub (hv.continuous.intervalIntegrable 0 L)
      (continuous_const.intervalIntegrable 0 L)] at hi
    simpa [ell, intervalIntegral.integral_const, abs_of_pos hL, Real.norm_eq_abs] using hi
  have hmnear : |m - 1| ≤ δ := by
    have heq : m - 1 = (ell - L) / L := by dsimp [m]; field_simp
    rw [heq, abs_div, abs_of_pos hL]
    exact (div_le_iff₀ hL).2 hellnear
  have hmlo : (1 : ℝ) / 2 ≤ m := by
    have := (abs_le.mp hmnear).1
    linarith
  have hmhi : m ≤ (3 : ℝ) / 2 := by
    have := (abs_le.mp hmnear).2
    linarith
  have hvlo (x : ℝ) : (1 : ℝ) / 2 ≤ v x := by
    have := (abs_le.mp (hvnear x)).1
    linarith
  have hvm (x : ℝ) : |v x - m| ≤ 2 * δ := by
    calc
      |v x - m| ≤ |v x - 1| + |1 - m| := abs_sub_le _ _ _
      _ ≤ δ + δ := add_le_add (hvnear x) (by simpa [abs_sub_comm] using hmnear)
      _ = 2 * δ := by ring
  have hd' (x : ℝ) : HasDerivAt phi (v x / m) x := by
    convert (hd x).1 using 1
    dsimp [m, ell]
    field_simp
  have hid' (x : ℝ) : HasDerivAt phi.symm (m / v (phi.symm x)) x := by
    convert (hid x).1 using 1
    dsimp [m, ell]
    field_simp
  have hderiv : deriv phi = fun x => v x / m := funext fun x => (hd' x).deriv
  have hinderiv : deriv phi.symm = fun x => m / v (phi.symm x) :=
    funext fun x => (hid' x).deriv
  have hsmooth : ContDiff ℝ ∞ (phi : ℝ → ℝ) :=
    contDiff_infty_iff_deriv.mpr
      ⟨hphi.differentiable (by norm_num), hderiv ▸ hv.div_const m⟩
  have hismooth : ContDiff ℝ ∞ (phi.symm : ℝ → ℝ) :=
    phi.contDiff_symm_deriv (fun x => (div_pos (hpos x) hmpos).ne') hd' hsmooth
  have hdd (x : ℝ) : HasDerivAt (deriv phi) (deriv v x / m) x := by
    rw [hderiv]
    exact ((hv.differentiable (by simp) x).hasDerivAt).div_const m
  have hidd (x : ℝ) : HasDerivAt (deriv phi.symm)
      (-(m ^ 2 * deriv v (phi.symm x)) / v (phi.symm x) ^ 3) x := by
    rw [hinderiv]
    have hc := ((hv.differentiable (by simp) (phi.symm x)).hasDerivAt).comp x (hid' x)
    convert (hasDerivAt_const x m).div hc (hpos _).ne' using 1 <;>
      first | rfl | (simp only [Function.comp_apply]; field_simp; ring)
  have hfirst (x : ℝ) : |deriv phi x - 1| ≤ 4 * δ := by
    rw [(hd' x).deriv, div_sub_one hmpos.ne', abs_div, abs_of_pos hmpos]
    apply (div_le_iff₀ hmpos).2
    have h := mul_le_mul_of_nonneg_left hmlo (show 0 ≤ 4 * δ by positivity)
    nlinarith [hvm x]
  have hsecond (x : ℝ) : |deriv (deriv phi) x| ≤ 2 * δ := by
    rw [(hdd x).deriv, abs_div, abs_of_pos hmpos]
    apply (div_le_iff₀ hmpos).2
    have h := mul_le_mul_of_nonneg_left hmlo (show 0 ≤ 2 * δ by positivity)
    nlinarith [hvderiv x]
  have hifirst (x : ℝ) : |deriv phi.symm x - 1| ≤ 4 * δ := by
    rw [(hid' x).deriv, div_sub_one (hpos _).ne', abs_div, abs_of_pos (hpos _)]
    apply (div_le_iff₀ (hpos _)).2
    have h := mul_le_mul_of_nonneg_left (hvlo (phi.symm x))
      (show 0 ≤ 4 * δ by positivity)
    nlinarith [show |m - v (phi.symm x)| ≤ 2 * δ by
      simpa only [abs_sub_comm] using hvm (phi.symm x)]
  have hisecond (x : ℝ) : |deriv (deriv phi.symm) x| ≤ 18 * δ := by
    rw [(hidd x).deriv, abs_div, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg m),
      abs_of_pos (pow_pos (hpos _) 3)]
    apply (div_le_iff₀ (pow_pos (hpos _) 3)).2
    have hm2 : m ^ 2 ≤ (9 : ℝ) / 4 := by nlinarith
    have hv3 : (1 : ℝ) / 8 ≤ v (phi.symm x) ^ 3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (hvlo (phi.symm x)) 3
      norm_num at h ⊢
      exact h
    calc
      m ^ 2 * |deriv v (phi.symm x)| ≤ m ^ 2 * δ :=
        mul_le_mul_of_nonneg_left (hvderiv _) (sq_nonneg m)
      _ ≤ (9 / 4) * δ := mul_le_mul_of_nonneg_right hm2 hδ
      _ ≤ 18 * δ * v (phi.symm x) ^ 3 := by
        have h := mul_le_mul_of_nonneg_left hv3 (show 0 ≤ 18 * δ by positivity)
        nlinarith
  have hprimitive (x : ℝ) : phi x - x =
      (1 / m) * ∫ y in (0 : ℝ)..x, v y - m := by
    rw [hformula, intervalIntegral.integral_sub (hv.continuous.intervalIntegrable 0 x)
      (continuous_const.intervalIntegrable 0 x), intervalIntegral.integral_const]
    dsimp [m, ell]
    simp only [sub_zero]
    field_simp
  have hdispl0 (x : ℝ) (hx : x ∈ Icc 0 L) : |phi x - x| ≤ 4 * L * δ := by
    have hi : |∫ y in (0 : ℝ)..x, v y - m| ≤ 2 * δ * x := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := x) (fun y _ => show ‖v y - m‖ ≤ 2 * δ from hvm y)
      simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hx.1] using h
    have hinv : 1 / m ≤ 2 := (div_le_iff₀ hmpos).2 (by linarith)
    rw [hprimitive, abs_mul, abs_of_pos (div_pos one_pos hmpos)]
    calc
      (1 / m) * |∫ y in (0 : ℝ)..x, v y - m| ≤ (1 / m) * (2 * δ * x) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ ≤ (1 / m) * (2 * δ * L) := by gcongr; exact hx.2
      _ ≤ 2 * (2 * δ * L) := mul_le_mul_of_nonneg_right hinv (by positivity)
      _ = 4 * L * δ := by ring
  have hdisplper : Function.Periodic (fun x => phi x - x) L := by
    intro x
    change phi (x + L) - (x + L) = phi x - x
    rw [hshift]
    ring
  have hdispl (x : ℝ) : |phi x - x| ≤ 4 * L * δ := by
    have heq : phi x - x = phi (toIcoMod hL 0 x) - toIcoMod hL 0 x := by
      calc
        phi x - x = (fun y => phi y - y)
            (toIcoMod hL 0 x + toIcoDiv hL 0 x • L) :=
          congrArg (fun y => phi y - y) (toIcoMod_add_toIcoDiv_zsmul hL 0 x).symm
        _ = _ := hdisplper.zsmul (toIcoDiv hL 0 x) (toIcoMod hL 0 x)
    rw [heq]
    exact hdispl0 _ ⟨(toIcoMod_mem_Ico' hL x).1, (toIcoMod_mem_Ico' hL x).2.le⟩
  have hidispl (x : ℝ) : |phi.symm x - x| ≤ 4 * L * δ := by
    have heq : phi.symm x - x = -(phi (phi.symm x) - phi.symm x) := by
      rw [phi.apply_symm_apply]
      ring
    rw [heq, abs_neg]
    exact hdispl _
  exact ⟨hell, hmnear, phi, hformula, hsmooth, hismooth, hzero, hshift, hinvshift,
    hd', hdd, hid', hidd, fun x => ⟨(hd x).2, (hid x).2⟩, hdispl, hfirst,
    hsecond, hidispl, hifirst, hisecond⟩

end PoincareConjecture.M63
