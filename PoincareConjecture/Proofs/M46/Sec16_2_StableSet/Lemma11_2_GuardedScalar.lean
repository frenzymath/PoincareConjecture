import PoincareConjecture.Proofs.M44.Mathlib.GuardedScalarComparison

set_option autoImplicit false

open Set

namespace PoincareConjecture.Proofs.M46

theorem le_two_inv_sq_of_deriv_le_threeHalves_above
    {f f' : ℝ → ℝ} {a b B r : ℝ} (hB : 0 < B) (hr : 0 < r)
    (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ s ∈ Ico a b, HasDerivWithinAt f (f' s) (Ici s) s)
    (hinitial : f a ≤ r⁻¹ ^ 2)
    (hrate : ∀ s ∈ Ico a b, r⁻¹ ^ 2 ≤ f s → f' s ≤ B * f s ^ (3 / 2 : ℝ))
    (hlength : 8 * B * (b - a) ≤ r) :
    ∀ s ∈ Icc a b, f s ≤ 2 * r⁻¹ ^ 2 := by
  let q := r⁻¹
  have hq : 0 < q := inv_pos.mpr hr
  have hrq : r * q = 1 := mul_inv_cancel₀ hr.ne'
  let barrier (s : ℝ) := q ^ 2 + 8 * B * q ^ 3 * (s - a)
  have hbounds (s : ℝ) (hs : s ∈ Icc a b) :
      q ^ 2 ≤ barrier s ∧ barrier s ≤ 2 * q ^ 2 := by
    have hsa : 0 ≤ s - a := sub_nonneg.mpr hs.1
    have hlo : 0 ≤ 8 * B * q ^ 3 * (s - a) := by positivity
    have hlen : 8 * B * (s - a) ≤ r :=
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hs.2 a) (by positivity)).trans hlength
    have hmul := mul_le_mul_of_nonneg_right hlen (by positivity : 0 ≤ q ^ 3)
    have hcancel : r * q ^ 3 = q ^ 2 := by calc
      r * q ^ 3 = (r * q) * q ^ 2 := by ring
      _ = q ^ 2 := by rw [hrq, one_mul]
    rw [hcancel] at hmul
    dsimp only [barrier]
    constructor <;> nlinarith
  have hbarrier (s : ℝ) : HasDerivAt barrier (8 * B * q ^ 3) s := by
    simpa only [barrier, id_eq, mul_one] using
      (((hasDerivAt_id s).sub_const a).const_mul (8 * B * q ^ 3)).const_add (q ^ 2)
  have hle : ∀ s ∈ Icc a b, f s ≤ barrier s := by
    apply image_le_of_deriv_right_lt_deriv_boundary hcont hderiv
    · simpa only [barrier, sub_self, mul_zero, add_zero] using hinitial
    · exact hbarrier
    · intro s hs heq
      obtain ⟨hlo, hhi⟩ := hbounds s ⟨hs.1, hs.2.le⟩
      have hflo : q ^ 2 ≤ f s := by rwa [heq]
      have hfhi : f s ≤ 2 * q ^ 2 := by rwa [heq]
      have hfpos : 0 < f s := (sq_pos_of_pos hq).trans_le hflo
      have hsqrt : Real.sqrt (f s) ≤ 2 * q := by
        apply (Real.sqrt_le_iff).mpr
        exact ⟨by positivity, by nlinarith [sq_nonneg q]⟩
      have hrpow : f s ^ (3 / 2 : ℝ) = f s * Real.sqrt (f s) := by
        rw [show (3 / 2 : ℝ) = 1 + (1 / 2 : ℝ) by norm_num,
          Real.rpow_add hfpos, Real.rpow_one, ← Real.sqrt_eq_rpow]
      have hpower : f s ^ (3 / 2 : ℝ) ≤ 4 * q ^ 3 := by
        rw [hrpow]
        have hmul := mul_le_mul hfhi hsqrt (Real.sqrt_nonneg _) (by positivity : 0 ≤ 2 * q ^ 2)
        nlinarith
      have hbound := (hrate s hs hflo).trans (mul_le_mul_of_nonneg_left hpower hB.le)
      have hpositive : 0 < B * q ^ 3 := mul_pos hB (pow_pos hq _)
      nlinarith
  intro s hs
  exact (hle s hs).trans (hbounds s hs).2

theorem le_four_inv_sq_of_deriv_le_sq_above
    {f f' : ℝ → ℝ} {a b B r : ℝ} (hB : 0 < B) (hr : 0 < r)
    (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ s ∈ Ico a b, HasDerivWithinAt f (f' s) (Ici s) s)
    (hinitial : f a ≤ 2 * r⁻¹ ^ 2)
    (hrate : ∀ s ∈ Ico a b, r⁻¹ ^ 2 ≤ f s → f' s ≤ B * f s ^ 2)
    (htime : 16 * B * r⁻¹ ^ 2 * (b - a) ≤ 1) :
    ∀ s ∈ Icc a b, f s ≤ 4 * r⁻¹ ^ 2 := by
  have h := le_two_mul_of_deriv_le_sq_above hB
    (by positivity : 0 < 2 * r⁻¹ ^ 2)
    (by nlinarith [sq_nonneg r⁻¹] : r⁻¹ ^ 2 ≤ 2 * r⁻¹ ^ 2)
    hcont hderiv hinitial hrate
    (by nlinarith : 8 * B * (2 * r⁻¹ ^ 2) * (b - a) ≤ 1)
  intro s hs
  have hvalue := h s hs
  nlinarith

end PoincareConjecture.Proofs.M46
