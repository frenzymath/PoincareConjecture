import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity













namespace PoincareConjecture.RicciFlow.Splitting.MaximumPrinciple.Barrier


noncomputable def boundaryScale (rho lam H0 : ℝ) : ℝ :=
  min (rho ^ 2 / 2) (min (1 / 4) (lam * rho ^ 2 / (2 * (H0 + 1))))


theorem boundaryScale_bounds {rho lam H0 : ℝ}
    (hrho : 0 < rho) (hlam : 0 < lam) (hH0 : 0 ≤ H0) :
    0 < boundaryScale rho lam H0 ∧
      boundaryScale rho lam H0 ≤ rho ^ 2 / 2 ∧
      boundaryScale rho lam H0 ≤ 1 / 4 ∧
      2 * H0 * boundaryScale rho lam H0 ^ 2 ≤ lam * rho ^ 2 := by
  let d := boundaryScale rho lam H0
  have hd : 0 < d := by dsimp [d, boundaryScale]; positivity
  have hdr : d ≤ rho ^ 2 / 2 := min_le_left _ _
  have hdq : d ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hdf : d ≤ lam * rho ^ 2 / (2 * (H0 + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hden : 0 < 2 * (H0 + 1) := by positivity
  have hmul := (le_div_iff₀ hden).mp hdf
  have hd2 : d ^ 2 ≤ d := by nlinarith
  have hHmul := mul_le_mul_of_nonneg_left hd2 hH0
  exact ⟨hd, hdr, hdq, by dsimp [d] at *; nlinarith⟩


noncomputable def dampingConstant (rho lam Lam H0 : ℝ) : ℝ :=
  8 * Lam * rho ^ 2 / boundaryScale rho lam H0 ^ 3 +
    2 * H0 / boundaryScale rho lam H0 ^ 2


theorem dampingConstant_nonneg {rho lam Lam H0 : ℝ}
    (hrho : 0 < rho) (hlam : 0 < lam) (hLam : lam ≤ Lam) (hH0 : 0 ≤ H0) :
    0 ≤ dampingConstant rho lam Lam H0 := by
  have hd := (boundaryScale_bounds hrho hlam hH0).1
  have hLam0 : 0 < Lam := lt_of_lt_of_le hlam hLam
  unfold dampingConstant
  positivity

private theorem near_boundary_nonneg {rho lam H0 d s Q H : ℝ}
    (hlam : 0 < lam) (hH0 : 0 ≤ H0) (hs : 0 < s) (hsd : s ≤ d)
    (hdr : d ≤ rho ^ 2 / 2) (hdq : d ≤ 1 / 4)
    (hdH : 2 * H0 * d ^ 2 ≤ lam * rho ^ 2)
    (hQ : lam * (rho ^ 2 - s) ≤ Q) (hH : H ≤ H0) :
    0 ≤ 4 * Q / s ^ 4 - 8 * Q / s ^ 3 - 2 * H / s ^ 2 := by
  have hr : rho ^ 2 / 2 ≤ rho ^ 2 - s := by linarith
  have hlr := mul_le_mul_of_nonneg_left hr hlam.le
  have hQ0 : 0 ≤ Q := by nlinarith [sq_nonneg rho]
  have hQs : 8 * Q * s ≤ 2 * Q := by nlinarith
  have hs2 : s ^ 2 ≤ d ^ 2 := by nlinarith
  have hH2 := mul_le_mul_of_nonneg_left hs2 hH0
  have hHs := mul_le_mul_of_nonneg_right hH (sq_nonneg s)
  have hnum : 0 ≤ 4 * Q - 8 * Q * s - 2 * H * s ^ 2 := by nlinarith
  have hid : 4 * Q / s ^ 4 - 8 * Q / s ^ 3 - 2 * H / s ^ 2 =
      (4 * Q - 8 * Q * s - 2 * H * s ^ 2) / s ^ 4 := by
    field_simp
  rw [hid]
  exact div_nonneg hnum (pow_nonneg hs.le _)



theorem radial_coefficient_nonneg {rho lam Lam H0 s Q H : ℝ}
    (hrho : 0 < rho) (hlam : 0 < lam) (hLam : lam ≤ Lam) (hH0 : 0 ≤ H0)
    (hs : 0 < s) (hsrho : s ≤ rho ^ 2)
    (hQlo : lam * (rho ^ 2 - s) ≤ Q)
    (hQhi : Q ≤ Lam * (rho ^ 2 - s)) (hH : H ≤ H0) :
    0 ≤ dampingConstant rho lam Lam H0 + 4 * Q / s ^ 4 -
      8 * Q / s ^ 3 - 2 * H / s ^ 2 := by
  obtain ⟨hd, hdr, hdq, hdH⟩ := boundaryScale_bounds hrho hlam hH0
  have hC := dampingConstant_nonneg hrho hlam hLam hH0
  by_cases hsd : s ≤ boundaryScale rho lam H0
  · have hn := near_boundary_nonneg hlam hH0 hs hsd hdr hdq hdH hQlo hH
    linarith
  · have hds := le_of_lt (lt_of_not_ge hsd)
    have hLam0 : 0 ≤ Lam := (lt_of_lt_of_le hlam hLam).le
    have hQ0 : 0 ≤ Q := (mul_nonneg hlam.le (sub_nonneg.mpr hsrho)).trans hQlo
    have hQr : Q ≤ Lam * rho ^ 2 := by nlinarith
    have hpow3 : boundaryScale rho lam H0 ^ 3 ≤ s ^ 3 :=
      pow_le_pow_left₀ hd.le hds 3
    have hpow2 : boundaryScale rho lam H0 ^ 2 ≤ s ^ 2 :=
      pow_le_pow_left₀ hd.le hds 2
    have hQdiv : 8 * Q / s ^ 3 ≤
        8 * Lam * rho ^ 2 / boundaryScale rho lam H0 ^ 3 := by
      calc
        8 * Q / s ^ 3 ≤ (8 * Lam * rho ^ 2) / s ^ 3 :=
          div_le_div_of_nonneg_right (by nlinarith) (pow_nonneg hs.le _)
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hpow3
    have hHdiv : 2 * H / s ^ 2 ≤ 2 * H0 / boundaryScale rho lam H0 ^ 2 := by
      calc
        2 * H / s ^ 2 ≤ 2 * H0 / s ^ 2 :=
          div_le_div_of_nonneg_right (by linarith) (sq_nonneg s)
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hpow2
    have hpos : 0 ≤ 4 * Q / s ^ 4 := by positivity
    unfold dampingConstant
    linarith


theorem radial_coefficient_nonneg_of_radius_sq {rho lam Lam H0 s r2 Q H : ℝ}
    (hrho : 0 < rho) (hlam : 0 < lam) (hLam : lam ≤ Lam) (hH0 : 0 ≤ H0)
    (hs : 0 < s) (hsrho : s ≤ rho ^ 2) (hr2 : r2 = rho ^ 2 - s)
    (hQlo : lam * r2 ≤ Q) (hQhi : Q ≤ Lam * r2) (hH : H ≤ H0) :
    0 ≤ dampingConstant rho lam Lam H0 + 4 * Q / s ^ 4 -
      8 * Q / s ^ 3 - 2 * H / s ^ 2 := by
  subst r2
  exact radial_coefficient_nonneg hrho hlam hLam hH0 hs hsrho hQlo hQhi hH

end PoincareConjecture.RicciFlow.Splitting.MaximumPrinciple.Barrier
