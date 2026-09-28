import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CriticalGraph.Radial.Parameters

noncomputable section
set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies

private theorem radius_le_one {u : Real} (hu : 0 ≤ u) :
    minimumCapSquaredRadius u ≤ 1 := by
  by_cases hhalf : u ≤ 1 / 2
  · have hm := strictMonoOn_minimumCapSquaredRadius.monotoneOn ⟨hu, hhalf⟩
      (show (1 / 2 : Real) ∈ Icc (0 : Real) (1 / 2) by norm_num) hhalf
    simpa only [minimumCapSquaredRadius_eq_one le_rfl] using hm
  · rw [minimumCapSquaredRadius_eq_one (le_of_not_ge hhalf)]

theorem minimumCapLowerRadius_equation {t : Real} (ht : t ∈ Icc (-1 : Real) 0) :
    minimumCapLowerRadius t * t ∈ Icc (-2 : Real) 0 ∧
      minimumCapLowerRadius t ^ 2 * (1 - t ^ 2) =
        minimumCapSquaredRadius (minimumCapLowerRadius t * t + 2) := by
  by_cases hl : t < -4 / 5
  · have ht' : t ∈ Ioo (-21 / 20 : Real) (-3 / 4) := ⟨by linarith [ht.1], by linarith⟩
    have ht0 : t ≠ 0 := by linarith
    have hz : 0 ≤ (1 - t ^ 2) / t ^ 2 := div_nonneg (by nlinarith [ht.1, ht.2]) (sq_nonneg t)
    have hz1 : (1 - t ^ 2) / t ^ 2 < 1 := by
      apply (div_lt_iff₀ (sq_pos_of_ne_zero ht0)).mpr
      nlinarith
    have hu0 := minimumCapRayHeight_nonneg hz hz1
    have hu1 := (minimumCapRayHeight_spec (show
      (1 - t ^ 2) / t ^ 2 ∈ Ioo (-1 / 9 : Real) 1 from ⟨by linarith, hz1⟩)).1.2
    rw [minimumCapLowerRadius, if_pos hl, minimumCapRayFactor_height ht0]
    constructor
    · constructor <;> linarith
    · simpa only [sub_add_cancel] using minimumCapRayFactor_projection_sq ht'
  · have hrad : 0 < 1 - t ^ 2 := by nlinarith [ht.2]
    have hroot := Real.sq_sqrt hrad.le
    have hrootpos := Real.sqrt_pos.mpr hrad
    have hrootlow : 3 / 5 ≤ Real.sqrt (1 - t ^ 2) := by
      nlinarith [ht.2]
    have hinv : (Real.sqrt (1 - t ^ 2))⁻¹ ≤ 5 / 3 := by
      rw [← one_div, div_le_iff₀ hrootpos]
      linarith
    have hlower : -4 / 3 ≤ (Real.sqrt (1 - t ^ 2))⁻¹ * t := by
      have hm := mul_le_mul_of_nonpos_right hinv ht.2
      linarith
    have hupper : (Real.sqrt (1 - t ^ 2))⁻¹ * t ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hrootpos.le) ht.2
    rw [minimumCapLowerRadius, if_neg hl]
    refine ⟨⟨by linarith, hupper⟩, ?_⟩
    rw [minimumCapSquaredRadius_eq_one (by linarith)]
    rw [inv_pow, hroot, inv_mul_cancel₀ hrad.ne']

theorem minimumCapLowerRadius_eq_of_equation {t u l : Real}
    (ht : t ∈ Icc (-1 : Real) 0) (hu : u ∈ Icc (0 : Real) 2) (hl : 0 < l)
    (hheight : l * t = u - 2)
    (hprojection : l ^ 2 * (1 - t ^ 2) = minimumCapSquaredRadius u) :
    minimumCapLowerRadius t = l := by
  have hsq : l ^ 2 * t ^ 2 = (u - 2) ^ 2 := by rw [← mul_pow, hheight]
  have hratio (ht0 : t ≠ 0) (hu2 : u ≠ 2) :
      minimumCapRayRatio u = (1 - t ^ 2) / t ^ 2 := by
    unfold minimumCapRayRatio
    rw [← hprojection, show (2 - u) ^ 2 = l ^ 2 * t ^ 2 by nlinarith [hsq]]
    field_simp
  by_cases htcut : t < -4 / 5
  · have hu1 : u < 1 := by
      by_contra hn
      rw [minimumCapSquaredRadius_eq_one (by linarith)] at hprojection
      have huabs : (u - 2) ^ 2 ≤ 1 := by nlinarith [hu.2]
      have ht2 : 16 / 25 < t ^ 2 := by nlinarith
      have hm := mul_pos (sq_pos_of_pos hl) (sub_pos.mpr ht2)
      nlinarith [sq_nonneg l]
    have ht0 : t ≠ 0 := by linarith
    have hz0 : 0 ≤ (1 - t ^ 2) / t ^ 2 :=
      div_nonneg (by nlinarith [ht.1, ht.2]) (sq_nonneg _)
    have hz1 : (1 - t ^ 2) / t ^ 2 < 1 := by
      apply (div_lt_iff₀ (sq_pos_of_ne_zero ht0)).mpr
      nlinarith
    have hInv := minimumCapRayHeight_eq_of_ratio
      (show (1 - t ^ 2) / t ^ 2 ∈ Ioo (-1 / 9 : Real) 1 from ⟨by linarith, hz1⟩)
      ⟨by linarith [hu.1], hu1⟩ (hratio ht0 (by linarith))
    rw [minimumCapLowerRadius, if_pos htcut, minimumCapRayFactor, hInv]
    apply (div_eq_iff (neg_ne_zero.mpr ht0)).mpr
    linarith
  · have huhalf : 1 / 2 ≤ u := by
      by_contra hn
      have hu1 : u < 1 / 2 := lt_of_not_ge hn
      have hR := radius_le_one hu.1
      have ht2 : t ^ 2 ≤ 16 / 25 := by nlinarith [ht.2]
      have hm := mul_nonneg (sq_nonneg l) (sub_nonneg.mpr ht2)
      have huabs : 9 / 4 < (u - 2) ^ 2 := by nlinarith
      nlinarith
    rw [minimumCapSquaredRadius_eq_one huhalf] at hprojection
    have hrad : 0 < 1 - t ^ 2 := by nlinarith [sq_nonneg l]
    have hroot := Real.sq_sqrt hrad.le
    have he : l * Real.sqrt (1 - t ^ 2) = 1 := by
      have hm := mul_pos hl (Real.sqrt_pos.mpr hrad)
      nlinarith [sq_nonneg (l * Real.sqrt (1 - t ^ 2) - 1)]
    rw [minimumCapLowerRadius, if_neg htcut, ← one_div]
    exact ((eq_div_iff (Real.sqrt_pos.mpr hrad).ne').mpr he).symm

end Poincare.Manifold.Schoenflies
