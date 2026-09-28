import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PoincareConjecture.ReducedLengthBounds

noncomputable def pathDistanceScale (A τ s : ℝ) : ℝ :=
  Real.sqrt (A * Real.sqrt τ) / (Real.sqrt s * Real.sqrt (Real.sqrt s))

theorem pathDistanceScale_pos {A τ s : ℝ} (hA : 0 < A) (hτ : 0 < τ) (hs : 0 < s) :
    0 < pathDistanceScale A τ s := by
  dsimp [pathDistanceScale]
  positivity

theorem pathDistanceScale_sq {A τ s : ℝ} (hA : 0 ≤ A) (_hτ : 0 ≤ τ) (hs : 0 < s) :
    pathDistanceScale A τ s ^ 2 = A * Real.sqrt τ / (s * Real.sqrt s) := by
  simp only [pathDistanceScale, div_pow, mul_pow, Real.sq_sqrt (Real.sqrt_nonneg s),
    Real.sq_sqrt hs.le, Real.sq_sqrt (mul_nonneg hA (Real.sqrt_nonneg τ))]

theorem time_mul_pathDistanceScale_sq {A τ s : ℝ}
    (hA : 0 ≤ A) (hτ : 0 ≤ τ) (hs : 0 < s) :
    s * pathDistanceScale A τ s ^ 2 = A * Real.sqrt τ / Real.sqrt s := by
  rw [pathDistanceScale_sq hA hτ hs]
  field_simp

theorem one_le_time_sq_mul_pathDistanceScale_fourth {A τ s : ℝ}
    (hA : 1 ≤ A) (hs : 0 < s) (hsτ : s ≤ τ) :
    1 ≤ s ^ 2 * pathDistanceScale A τ s ^ 4 := by
  have hτ : 0 < τ := hs.trans_le hsτ
  have heq : s ^ 3 * pathDistanceScale A τ s ^ 4 = A ^ 2 * τ := by
    rw [show pathDistanceScale A τ s ^ 4 = (pathDistanceScale A τ s ^ 2) ^ 2 by ring,
      pathDistanceScale_sq (by linarith) hτ.le hs, div_pow]
    simp only [mul_pow, Real.sq_sqrt hτ.le, Real.sq_sqrt hs.le]
    field_simp
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  have hright : s ≤ A ^ 2 * τ := hsτ.trans (by nlinarith)
  apply (mul_le_mul_iff_of_pos_left hs).mp
  nlinarith [heq]

theorem pathDistanceScale_ricci_coefficient_le {A τ s : ℝ} {n : ℕ}
    (hA : 1 ≤ A) (hs : 0 < s) (hsτ : s ≤ τ) :
    2 * (n : ℝ) * pathDistanceScale A τ s +
      24 * (A * Real.sqrt τ / Real.sqrt s) / (s * pathDistanceScale A τ s) +
      576 / (s ^ 2 * pathDistanceScale A τ s ^ 3) ≤
        (2 * (n : ℝ) + 600) * pathDistanceScale A τ s := by
  have hc := pathDistanceScale_pos (by linarith : 0 < A) (hs.trans_le hsτ) hs
  have hsq := time_mul_pathDistanceScale_sq (by linarith : 0 ≤ A) (hs.trans_le hsτ).le hs
  have hquart := one_le_time_sq_mul_pathDistanceScale_fourth hA hs hsτ
  have hmid : 24 * (A * Real.sqrt τ / Real.sqrt s) /
      (s * pathDistanceScale A τ s) = 24 * pathDistanceScale A τ s := by
    rw [← hsq]
    field_simp
  have hlast : 576 / (s ^ 2 * pathDistanceScale A τ s ^ 3) ≤
      576 * pathDistanceScale A τ s := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [hquart]
  rw [hmid]
  nlinarith

theorem hasDerivAt_fourthRootScale {A τ s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t => 4 * Real.sqrt (A * Real.sqrt τ) * Real.sqrt (Real.sqrt t))
      (pathDistanceScale A τ s) s := by
  have hd := (Real.hasDerivAt_sqrt (Real.sqrt_pos.mpr hs).ne').comp s
    (Real.hasDerivAt_sqrt hs.ne')
  convert! hd.const_mul (4 * Real.sqrt (A * Real.sqrt τ)) using 1
  dsimp [pathDistanceScale]
  ring

end PoincareConjecture.ReducedLengthBounds
