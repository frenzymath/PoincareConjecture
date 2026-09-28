import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.Isometry

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X]

theorem radial_sq_eq_of_minimizing_between
    (o x z y : X) (dilate : ℝ → X → X)
    (hcone : ∀ a : ℝ, 0 < a → ∀ p q : X,
      dist p (dilate a q) ^ 2 = a ^ 2 * dist o q ^ 2 + dist o p ^ 2 -
        a * (dist o q ^ 2 + dist o p ^ 2 - dist p q ^ 2))
    (hxz : 0 < dist x z) (hzy : 0 < dist z y)
    (hbetween : dist x y = dist x z + dist z y) :
    dist x y * dist o z ^ 2 = dist z y * dist o x ^ 2 + dist x z * dist o y ^ 2 -
      dist x y * dist x z * dist z y := by
  let P : X → ℝ → ℝ := fun p a =>
    a ^ 2 * dist o z ^ 2 + dist o p ^ 2 -
      a * (dist o z ^ 2 + dist o p ^ 2 - dist p z ^ 2)
  have hPone (p : X) : P p 1 = dist p z ^ 2 := by dsimp [P]; ring
  have hPsqrt (p : X) : Real.sqrt (P p 1) = dist p z := by
    rw [hPone, Real.sqrt_sq (dist_nonneg : 0 ≤ dist p z)]
  have hPdistance (p : X) {a : ℝ} (ha : 0 < a) :
      Real.sqrt (P p a) = dist p (dilate a z) := by
    rw [show P p a = dist p (dilate a z) ^ 2 from (hcone a ha p z).symm,
      Real.sqrt_sq dist_nonneg]
  have hPderiv (p : X) : HasDerivAt (P p)
      (dist o z ^ 2 - dist o p ^ 2 + dist p z ^ 2) 1 := by
    convert! ((((hasDerivAt_id (1 : ℝ)).pow 2).mul_const (dist o z ^ 2)).add
      (hasDerivAt_const 1 (dist o p ^ 2)) |>.sub
      ((hasDerivAt_id 1).mul_const (dist o z ^ 2 + dist o p ^ 2 - dist p z ^ 2))) using 1
    norm_num
    ring
  have hPx : P x 1 ≠ 0 := by rw [hPone]; exact pow_ne_zero 2 hxz.ne'
  have hPy : P y 1 ≠ 0 := by
    rw [hPone, dist_comm y z]
    exact pow_ne_zero 2 hzy.ne'
  let L : ℝ → ℝ := fun a => Real.sqrt (P x a) + Real.sqrt (P y a)
  have hmin : IsLocalMin L 1 := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with a ha
    change Real.sqrt (P x 1) + Real.sqrt (P y 1) ≤
      Real.sqrt (P x a) + Real.sqrt (P y a)
    rw [hPsqrt x, hPsqrt y, dist_comm y z, ← hbetween,
      hPdistance x ha, hPdistance y ha, dist_comm y (dilate a z)]
    exact dist_triangle x (dilate a z) y
  have hd := ((hPderiv x).sqrt hPx).add ((hPderiv y).sqrt hPy)
  have hzero := hmin.hasDerivAt_eq_zero hd
  rw [hPsqrt x, hPsqrt y, dist_comm y z] at hzero
  have hcancel :
      (dist o z ^ 2 - dist o x ^ 2 + dist x z ^ 2) * dist z y +
      (dist o z ^ 2 - dist o y ^ 2 + dist z y ^ 2) * dist x z = 0 := by
    field_simp [hxz.ne', hzy.ne'] at hzero
    nlinarith [hzero]
  rw [hbetween]
  nlinarith [hcancel]

theorem radial_sq_interpolation_of_minimizing_segment
    (o x y z : X) (dilate : ℝ → X → X)
    (hcone : ∀ a : ℝ, 0 < a → ∀ p q : X,
      dist p (dilate a q) ^ 2 = a ^ 2 * dist o q ^ 2 + dist o p ^ 2 -
        a * (dist o q ^ 2 + dist o p ^ 2 - dist p q ^ 2))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hxz : dist x z = t * dist x y) (hzy : dist z y = (1 - t) * dist x y) :
    dist o z ^ 2 = (1 - t) * dist o x ^ 2 + t * dist o y ^ 2 -
      t * (1 - t) * dist x y ^ 2 := by
  by_cases hxy : dist x y = 0
  · have hzx : z = x := (dist_eq_zero.mp (hxz.trans (by simp [hxy]))).symm
    have hyx : y = x := (dist_eq_zero.mp hxy).symm
    subst z
    subst y
    simp only [dist_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, sub_zero]
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
  have h := radial_sq_eq_of_minimizing_between o x z y dilate hcone hxzpos hzypos hbetween
  rw [hxz, hzy] at h
  apply mul_left_cancel₀ hxy
  nlinarith [h]

theorem radial_potential_on_minimizing_segment
    (o : X) (dilate : ℝ → X → X)
    (hcone : ∀ a : ℝ, 0 < a → ∀ p q : X,
      dist p (dilate a q) ^ 2 = a ^ 2 * dist o q ^ 2 + dist o p ^ 2 -
        a * (dist o q ^ 2 + dist o p ^ 2 - dist p q ^ 2))
    (γ : ℝ → X)
    (hγ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (γ s) (γ t) = |s - t| * dist (γ 0) (γ 1))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    dist o (γ t) ^ 2 / 2 = (1 - t) * (dist o (γ 0) ^ 2 / 2) +
      t * (dist o (γ 1) ^ 2 / 2) - t * (1 - t) * dist (γ 0) (γ 1) ^ 2 / 2 := by
  have hxz : dist (γ 0) (γ t) = t * dist (γ 0) (γ 1) := by
    simpa only [zero_sub, abs_neg, abs_of_nonneg ht.1] using hγ 0 (by simp) t ht
  have hzy : dist (γ t) (γ 1) = (1 - t) * dist (γ 0) (γ 1) := by
    simpa only [abs_of_nonpos (sub_nonpos.mpr ht.2), neg_sub] using hγ t ht 1 (by simp)
  have h := radial_sq_interpolation_of_minimizing_segment o (γ 0) (γ 1) (γ t)
    dilate hcone ht hxz hzy
  linarith

theorem radial_potential_on_isometric_segment
    (o : X) (dilate : ℝ → X → X)
    (hcone : ∀ a : ℝ, 0 < a → ∀ p q : X,
      dist p (dilate a q) ^ 2 = a ^ 2 * dist o q ^ 2 + dist o p ^ 2 -
        a * (dist o q ^ 2 + dist o p ^ 2 - dist p q ^ 2))
    {L : ℝ} (hL : 0 ≤ L) (γ : Icc (0 : ℝ) L → X) (hγ : Isometry γ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    dist o (γ ⟨t * L, ⟨mul_nonneg ht.1 hL, by nlinarith [ht.2]⟩⟩) ^ 2 / 2 =
      (1 - t) * (dist o (γ ⟨0, ⟨le_rfl, hL⟩⟩) ^ 2 / 2) +
      t * (dist o (γ ⟨L, ⟨hL, le_rfl⟩⟩) ^ 2 / 2) - t * (1 - t) * L ^ 2 / 2 := by
  let x := γ ⟨0, ⟨le_rfl, hL⟩⟩
  let y := γ ⟨L, ⟨hL, le_rfl⟩⟩
  let z := γ ⟨t * L, ⟨mul_nonneg ht.1 hL, by nlinarith [ht.2]⟩⟩
  have hxy : dist x y = L := by
    simp only [x, y, hγ.dist_eq, Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg hL]
  have hxz : dist x z = t * dist x y := by
    rw [hxy]
    simp only [x, z, hγ.dist_eq, Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg (mul_nonneg ht.1 hL)]
  have hzy : dist z y = (1 - t) * dist x y := by
    rw [hxy]
    have htl : t * L - L ≤ 0 := by nlinarith [ht.2]
    simp only [z, y, hγ.dist_eq, Subtype.dist_eq, Real.dist_eq, abs_of_nonpos htl]
    ring
  have h := radial_sq_interpolation_of_minimizing_segment o x y z dilate hcone ht hxz hzy
  rw [hxy] at h
  change dist o z ^ 2 / 2 = (1 - t) * (dist o x ^ 2 / 2) +
    t * (dist o y ^ 2 / 2) - t * (1 - t) * L ^ 2 / 2
  linarith

end Poincare.AncientVolume.ScalarRatio
