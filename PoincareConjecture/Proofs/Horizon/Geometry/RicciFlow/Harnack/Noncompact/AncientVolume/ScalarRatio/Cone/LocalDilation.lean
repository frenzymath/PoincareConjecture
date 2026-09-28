import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.QuadraticIdentity

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X]

theorem potential_eq_of_local_radial_variation
    (f : X → ℝ) (x z y : X)
    (hvariation : ∀ᶠ a : ℝ in 𝓝 1, ∃ w : X,
      dist x w ^ 2 = 2 * a ^ 2 * f z + 2 * f x -
        a * (2 * f z + 2 * f x - dist x z ^ 2) ∧
      dist y w ^ 2 = 2 * a ^ 2 * f z + 2 * f y -
        a * (2 * f z + 2 * f y - dist y z ^ 2))
    (hxz : 0 < dist x z) (hzy : 0 < dist z y)
    (hbetween : dist x y = dist x z + dist z y) :
    dist x y * f z = dist z y * f x + dist x z * f y -
      dist x y * dist x z * dist z y / 2 := by
  let P : X → ℝ → ℝ := fun p a =>
    2 * a ^ 2 * f z + 2 * f p - a * (2 * f z + 2 * f p - dist p z ^ 2)
  have hPone (p : X) : P p 1 = dist p z ^ 2 := by dsimp [P]; ring
  have hPsqrt (p : X) : Real.sqrt (P p 1) = dist p z := by
    rw [hPone, Real.sqrt_sq dist_nonneg]
  have hPderiv (p : X) : HasDerivAt (P p)
      (2 * f z - 2 * f p + dist p z ^ 2) 1 := by
    convert! ((((hasDerivAt_id (1 : ℝ)).pow 2).const_mul 2 |>.mul_const (f z)).add
      (hasDerivAt_const 1 (2 * f p)) |>.sub
      ((hasDerivAt_id 1).mul_const (2 * f z + 2 * f p - dist p z ^ 2))) using 1
    norm_num
    ring
  have hPx : P x 1 ≠ 0 := by rw [hPone]; exact pow_ne_zero 2 hxz.ne'
  have hPy : P y 1 ≠ 0 := by
    rw [hPone, dist_comm y z]
    exact pow_ne_zero 2 hzy.ne'
  let L : ℝ → ℝ := fun a => Real.sqrt (P x a) + Real.sqrt (P y a)
  have hmin : IsLocalMin L 1 := by
    filter_upwards [hvariation] with a ha
    obtain ⟨w, hxw, hyw⟩ := ha
    change Real.sqrt (P x 1) + Real.sqrt (P y 1) ≤
      Real.sqrt (P x a) + Real.sqrt (P y a)
    rw [hPsqrt x, hPsqrt y, dist_comm y z, ← hbetween,
      show P x a = dist x w ^ 2 from hxw.symm,
      show P y a = dist y w ^ 2 from hyw.symm,
      Real.sqrt_sq dist_nonneg, Real.sqrt_sq dist_nonneg, dist_comm y w]
    exact dist_triangle x w y
  have hzero := hmin.hasDerivAt_eq_zero
    (((hPderiv x).sqrt hPx).add ((hPderiv y).sqrt hPy))
  rw [hPsqrt x, hPsqrt y, dist_comm y z] at hzero
  have hcancel :
      (2 * f z - 2 * f x + dist x z ^ 2) * dist z y +
      (2 * f z - 2 * f y + dist z y ^ 2) * dist x z = 0 := by
    field_simp [hxz.ne', hzy.ne'] at hzero
    nlinarith [hzero]
  rw [hbetween]
  nlinarith [hcancel]

theorem potential_interpolation_of_local_radial_variation
    (f : X → ℝ) (x z y : X) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hxz : dist x z = t * dist x y) (hzy : dist z y = (1 - t) * dist x y)
    (hvariation : 0 < dist x z → 0 < dist z y →
      ∀ᶠ a : ℝ in 𝓝 1, ∃ w : X,
        dist x w ^ 2 = 2 * a ^ 2 * f z + 2 * f x -
          a * (2 * f z + 2 * f x - dist x z ^ 2) ∧
        dist y w ^ 2 = 2 * a ^ 2 * f z + 2 * f y -
          a * (2 * f z + 2 * f y - dist y z ^ 2)) :
    f z = (1 - t) * f x + t * f y - t * (1 - t) * dist x y ^ 2 / 2 := by
  by_cases hxy : dist x y = 0
  · have hzx : z = x := (dist_eq_zero.mp (hxz.trans (by simp [hxy]))).symm
    have hyx : y = x := (dist_eq_zero.mp hxy).symm
    subst z
    subst y
    simp only [dist_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
      zero_div, sub_zero]
    ring
  have hxypos : 0 < dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm hxy)
  by_cases ht0 : t = 0
  · have hzx : z = x := (dist_eq_zero.mp (hxz.trans (by simp [ht0]))).symm
    subst z
    simp [ht0]
  by_cases ht1 : t = 1
  · have hzy' : z = y := dist_eq_zero.mp (hzy.trans (by simp [ht1]))
    subst z
    simp [ht1]
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have htoneless : t < 1 := lt_of_le_of_ne ht.2 ht1
  have hxzpos : 0 < dist x z := by rw [hxz]; exact mul_pos htpos hxypos
  have hzypos : 0 < dist z y := by rw [hzy]; exact mul_pos (sub_pos.mpr htoneless) hxypos
  have hbetween : dist x y = dist x z + dist z y := by rw [hxz, hzy]; ring
  have h := potential_eq_of_local_radial_variation f x z y
    (hvariation hxzpos hzypos) hxzpos hzypos hbetween
  rw [hxz, hzy] at h
  apply mul_left_cancel₀ hxy
  nlinarith [h]

end Poincare.AncientVolume.ScalarRatio
