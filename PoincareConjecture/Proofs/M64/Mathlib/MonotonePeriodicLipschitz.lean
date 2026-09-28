import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic





noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal

namespace PoincareConjecture




theorem m64Monotone_lipschitz_of_periodic_interval
    {f : ℝ → ℝ} {P : ℝ} (hP : 0 < P) (hm : Monotone f)
    (hshift : ∀ x, f (x + P) = f x + P) {K : ℝ≥0}
    (hLip : LipschitzOnWith K f (Icc 0 P)) : LipschitzWith K f := by
  have hbound {x y : ℝ} (hx : x ∈ Icc 0 P) (hy : y ∈ Icc 0 P) (hxy : x ≤ y) :
      f y - f x ≤ (K : ℝ) * (y - x) := by
    have h := hLip.dist_le_mul y hy x hx
    simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hm hxy)),
      abs_of_nonneg (sub_nonneg.mpr hxy)] using h
  have hKP : P ≤ (K : ℝ) * P := by
    have h := hbound ⟨le_rfl, hP.le⟩ ⟨hP.le, le_rfl⟩ hP.le
    have hend : f P = f 0 + P := by simpa only [zero_add] using hshift 0
    simpa only [hend, add_sub_cancel_left, sub_zero] using h
  have hK : (1 : ℝ) ≤ K := (mul_le_mul_iff_left₀ hP).mp (by simpa using hKP)
  have hperiod : Function.Periodic (fun x => f x - x) P := by
    intro x
    change f (x + P) - (x + P) = f x - x
    rw [hshift]
    ring
  have hordered (x y : ℝ) (hxy : x ≤ y) : f y - f x ≤ (K : ℝ) * (y - x) := by
    let x0 := toIcoMod hP 0 x
    let y0 := toIcoMod hP 0 y
    let i := toIcoDiv hP 0 x
    let j := toIcoDiv hP 0 y
    have hx0 : x0 ∈ Ico 0 P := toIcoMod_mem_Ico' hP x
    have hy0 : y0 ∈ Ico 0 P := toIcoMod_mem_Ico' hP y
    have hx : x0 + (i : ℝ) * P = x := toIcoMod_add_toIcoDiv_mul hP 0 x
    have hy : y0 + (j : ℝ) * P = y := toIcoMod_add_toIcoDiv_mul hP 0 y
    have hfx : f x = f x0 + (i : ℝ) * P := by
      have h := hperiod.zsmul i x0
      simp only [zsmul_eq_mul] at h
      rw [hx] at h
      linarith
    have hfy : f y = f y0 + (j : ℝ) * P := by
      have h := hperiod.zsmul j y0
      simp only [zsmul_eq_mul] at h
      rw [hy] at h
      linarith
    have hij : i ≤ j := by
      dsimp [i, j]
      simp only [toIcoDiv_eq_floor, sub_zero]
      exact Int.floor_mono (div_le_div_of_nonneg_right hxy hP.le)
    by_cases heq : i = j
    · have hxy0 : x0 ≤ y0 := by rw [heq] at hx; linarith
      have h := hbound (Ico_subset_Icc_self hx0) (Ico_subset_Icc_self hy0) hxy0
      rw [heq] at hx hfx
      rw [hfx, hfy]
      nlinarith
    · have hgap : (0 : ℝ) ≤ (j : ℝ) - (i : ℝ) - 1 := by
        have hij' : i + 1 ≤ j := Int.add_one_le_iff.mpr (lt_of_le_of_ne hij heq)
        exact_mod_cast (show (0 : ℤ) ≤ j - i - 1 by omega)
      have hmid : ((j : ℝ) - (i : ℝ) - 1) * P ≤
          (K : ℝ) * (((j : ℝ) - (i : ℝ) - 1) * P) := by
        exact le_mul_of_one_le_left (mul_nonneg hgap hP.le) hK
      have hlo := hbound (Ico_subset_Icc_self hx0) ⟨hP.le, le_rfl⟩ hx0.2.le
      have hhi := hbound ⟨le_rfl, hP.le⟩ (Ico_subset_Icc_self hy0) hy0.1
      have hend : f P = f 0 + P := by simpa only [zero_add] using hshift 0
      rw [hend] at hlo
      rw [hfx, hfy]
      nlinarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rcases le_total x y with hxy | hyx
  · simpa only [Real.dist_eq, abs_sub_comm (f x) (f y), abs_sub_comm x y,
      abs_of_nonneg (sub_nonneg.mpr (hm hxy)), abs_of_nonneg (sub_nonneg.mpr hxy)]
      using hordered x y hxy
  · simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hm hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)] using hordered y x hyx

end PoincareConjecture
