import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CriticalGraph.ProfileInverse
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped ContDiff Topology

namespace Poincare.Manifold.Schoenflies

def minimumCapRayRatio (u : Real) : Real :=
  minimumCapSquaredRadius u / (2 - u) ^ 2

theorem contDiffAt_minimumCapRayRatio {u : Real} (hu : u < 2) :
    ContDiffAt Real ∞ minimumCapRayRatio u :=
  contDiff_minimumCapSquaredRadius.contDiffAt.div
    ((contDiffAt_const.sub contDiffAt_id).pow 2) (pow_ne_zero _ (by linarith))

theorem deriv_minimumCapRayRatio {u : Real} (hu : u < 2) :
    deriv minimumCapRayRatio u =
      (deriv minimumCapSquaredRadius u * (2 - u) + 2 * minimumCapSquaredRadius u) /
        (2 - u) ^ 3 := by
  have hd := (contDiff_minimumCapSquaredRadius.differentiable (by simp) u).hasDerivAt
  have he := hd.div (((hasDerivAt_const u (2 : Real)).sub (hasDerivAt_id u)).pow 2)
    (pow_ne_zero 2 (show 2 - u ≠ 0 by linarith))
  change HasDerivAt minimumCapRayRatio _ u at he
  rw [he.deriv]
  simp only [Nat.cast_ofNat, Pi.pow_apply, Pi.sub_apply, id_eq, Nat.reduceSub,
    pow_one, zero_sub, mul_neg, mul_one]
  field_simp [show 2 - u ≠ 0 by linarith]
  ring

theorem deriv_minimumCapRayRatio_pos {u : Real} (hu : u ∈ Ioo (-1 : Real) 1) :
    0 < deriv minimumCapRayRatio u := by
  rw [deriv_minimumCapRayRatio (by linarith [hu.2])]
  apply div_pos _ (pow_pos (by linarith [hu.2]) _)
  by_cases hu0 : u < 0
  · have heq : minimumCapSquaredRadius =ᶠ[𝓝 u] id := by
      filter_upwards [gt_mem_nhds (show u < 1 / 4 by linarith)] with x hx
      exact minimumCapSquaredRadius_eq_self hx.le
    rw [heq.deriv_eq, deriv_id, minimumCapSquaredRadius_eq_self (by linarith)]
    linarith [hu.1]
  have hu0' := le_of_not_gt hu0
  have hR : 0 ≤ minimumCapSquaredRadius u :=
    div_nonneg hu0' (minimumCapDenominator_pos u).le
  by_cases huhalf : u < 1 / 2
  · exact add_pos_of_pos_of_nonneg
      (mul_pos (deriv_minimumCapSquaredRadius_pos huhalf) (by linarith)) (by positivity)
  have hder : 0 ≤ deriv minimumCapSquaredRadius u := by
    rw [deriv_minimumCapSquaredRadius]
    apply div_nonneg _ (sq_nonneg _)
    have hw : minimumCapWeight u ≤ 1 := Real.smoothTransition.le_one _
    have hd : 0 ≤ deriv minimumCapWeight u := monotone_minimumCapWeight.deriv_nonneg
    exact add_nonneg (sub_nonneg.mpr hw)
      (mul_nonneg (mul_nonneg hu0' (by linarith [hu.2])) hd)
  rw [minimumCapSquaredRadius_eq_one (le_of_not_gt huhalf)]
  exact add_pos_of_nonneg_of_pos (mul_nonneg hder (by linarith [hu.2])) (by norm_num)

theorem strictMonoOn_minimumCapRayRatio :
    StrictMonoOn minimumCapRayRatio (Icc (-1 : Real) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · intro u hu
    exact (contDiffAt_minimumCapRayRatio (by linarith [hu.2])).continuousAt.continuousWithinAt
  · intro u hu
    rw [interior_Icc] at hu
    exact deriv_minimumCapRayRatio_pos hu

theorem minimumCapRayRatio_neg_one : minimumCapRayRatio (-1) = -1 / 9 := by
  rw [minimumCapRayRatio, minimumCapSquaredRadius_eq_self (by norm_num)]
  norm_num

theorem minimumCapRayRatio_zero : minimumCapRayRatio 0 = 0 := by
  rw [minimumCapRayRatio, minimumCapSquaredRadius_eq_self (by norm_num)]
  norm_num

theorem minimumCapRayRatio_half : minimumCapRayRatio (1 / 2) = 4 / 9 := by
  rw [minimumCapRayRatio, minimumCapSquaredRadius_eq_one le_rfl]
  norm_num

theorem minimumCapRayRatio_one : minimumCapRayRatio 1 = 1 := by
  rw [minimumCapRayRatio, minimumCapSquaredRadius_eq_one (by norm_num)]
  norm_num

theorem exists_unique_minimumCap_ray_height {z : Real} (hz : z ∈ Ioo (-1 / 9 : Real) 1) :
    ∃! u : Real, u ∈ Ioo (-1 : Real) 1 ∧ minimumCapRayRatio u = z := by
  have hc : ContinuousOn minimumCapRayRatio (Icc (-1 : Real) 1) := by
    intro u hu
    exact (contDiffAt_minimumCapRayRatio (by linarith [hu.2])).continuousAt.continuousWithinAt
  obtain ⟨u, hu, huz⟩ := intermediate_value_Icc (by norm_num : (-1 : Real) ≤ 1) hc
    (show z ∈ Icc (minimumCapRayRatio (-1)) (minimumCapRayRatio 1) by
      rw [minimumCapRayRatio_neg_one, minimumCapRayRatio_one]
      exact ⟨hz.1.le, hz.2.le⟩)
  have hu0 : -1 < u := lt_of_le_of_ne hu.1 (by
    intro he
    rw [← he, minimumCapRayRatio_neg_one] at huz
    linarith [hz.1])
  have hu1 : u < 1 := lt_of_le_of_ne hu.2 (by
    intro he
    rw [he, minimumCapRayRatio_one] at huz
    linarith [hz.2])
  refine ⟨u, ⟨⟨hu0, hu1⟩, huz⟩, ?_⟩
  rintro w ⟨hw, hwz⟩
  exact strictMonoOn_minimumCapRayRatio.injOn ⟨hw.1.le, hw.2.le⟩ hu (hwz.trans huz.symm)

def minimumCapRayHeight (z : Real) : Real :=
  if hz : z ∈ Ioo (-1 / 9 : Real) 1 then
    Classical.choose (exists_unique_minimumCap_ray_height hz) else z

theorem minimumCapRayHeight_spec {z : Real} (hz : z ∈ Ioo (-1 / 9 : Real) 1) :
    minimumCapRayHeight z ∈ Ioo (-1 : Real) 1 ∧
      minimumCapRayRatio (minimumCapRayHeight z) = z := by
  rw [minimumCapRayHeight, dif_pos hz]
  exact (Classical.choose_spec (exists_unique_minimumCap_ray_height hz)).1

theorem minimumCapRayHeight_eq_of_ratio {z u : Real} (hz : z ∈ Ioo (-1 / 9 : Real) 1)
    (hu : u ∈ Ioo (-1 : Real) 1) (he : minimumCapRayRatio u = z) :
    minimumCapRayHeight z = u :=
  (exists_unique_minimumCap_ray_height hz).unique (minimumCapRayHeight_spec hz) ⟨hu, he⟩

theorem minimumCapRayHeight_nonneg {z : Real} (hz : 0 ≤ z) (hz1 : z < 1) :
    0 ≤ minimumCapRayHeight z := by
  have hs := minimumCapRayHeight_spec (show z ∈ Ioo (-1 / 9 : Real) 1 from
    ⟨by linarith, hz1⟩)
  by_contra hn
  have hlt := strictMonoOn_minimumCapRayRatio ⟨hs.1.1.le, hs.1.2.le⟩
    (show (0 : Real) ∈ Icc (-1 : Real) 1 by norm_num) (lt_of_not_ge hn)
  rw [hs.2, minimumCapRayRatio_zero] at hlt
  exact (not_lt_of_ge hz) hlt

theorem minimumCapRayHeight_half_le {z : Real} (hz : 4 / 9 ≤ z) (hz1 : z < 1) :
    1 / 2 ≤ minimumCapRayHeight z := by
  have hs := minimumCapRayHeight_spec (show z ∈ Ioo (-1 / 9 : Real) 1 from
    ⟨by linarith, hz1⟩)
  by_contra hn
  have hlt := strictMonoOn_minimumCapRayRatio ⟨hs.1.1.le, hs.1.2.le⟩
    (show (1 / 2 : Real) ∈ Icc (-1 : Real) 1 by norm_num) (lt_of_not_ge hn)
  rw [hs.2, minimumCapRayRatio_half] at hlt
  exact (not_lt_of_ge hz) hlt

theorem contDiffAt_minimumCapRayHeight {z : Real} (hz : z ∈ Ioo (-1 / 9 : Real) 1) :
    ContDiffAt Real ∞ minimumCapRayHeight z := by
  let u := minimumCapRayHeight z
  have hu : u ∈ Ioo (-1 : Real) 1 := (minimumCapRayHeight_spec hz).1
  have hder : deriv minimumCapRayRatio u ≠ 0 := (deriv_minimumCapRayRatio_pos hu).ne'
  let L : Real ≃L[Real] Real :=
    (LinearEquiv.smulOfNeZero Real Real (deriv minimumCapRayRatio u) hder).toContinuousLinearEquiv
  have hf := contDiffAt_minimumCapRayRatio (show u < 2 by linarith [hu.2])
  have hd : HasFDerivAt minimumCapRayRatio L.toContinuousLinearMap u := by
    convert! (hf.differentiableAt (by simp)).hasFDerivAt using 1
    ext
    simp [L]
  let Q := hf.toOpenPartialHomeomorph minimumCapRayRatio hd (by simp)
  have huQ : u ∈ Q.source := hf.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hQu : Q u = z := (minimumCapRayHeight_spec hz).2
  have hzQ : z ∈ Q.target := hQu ▸ Q.map_source huQ
  have hQi : ContDiffAt Real ∞ Q.symm z := by
    have hi := hf.to_localInverse hd (by simp)
    change ContDiffAt Real ∞ Q.symm (minimumCapRayRatio u) at hi
    simpa only [show minimumCapRayRatio u = z from hQu] using hi
  have hQizu : Q.symm z = u := by rw [← hQu, Q.left_inv huQ]
  have hQirange : ∀ᶠ y in 𝓝 z, Q.symm y ∈ Ioo (-1 : Real) 1 :=
    hQi.continuousAt.eventually (isOpen_Ioo.mem_nhds (hQizu ▸ hu))
  apply hQi.congr_of_eventuallyEq
  filter_upwards [hQirange, Q.open_target.mem_nhds hzQ, isOpen_Ioo.mem_nhds hz]
    with y hy hyQ hyz
  exact minimumCapRayHeight_eq_of_ratio hyz hy (Q.right_inv hyQ)

def minimumCapRayFactor (t : Real) : Real :=
  (2 - minimumCapRayHeight ((1 - t ^ 2) / t ^ 2)) / (-t)

private theorem rayRatio_mem {t : Real} (ht : t ∈ Ioo (-21 / 20 : Real) (-3 / 4)) :
    (1 - t ^ 2) / t ^ 2 ∈ Ioo (-1 / 9 : Real) 1 := by
  have ht2 : 0 < t ^ 2 := sq_pos_of_neg (by linarith [ht.2])
  constructor
  · apply (lt_div_iff₀ ht2).mpr
    nlinarith [ht.1, ht.2]
  · apply (div_lt_iff₀ ht2).mpr
    nlinarith [ht.2]

theorem contDiffAt_minimumCapRayFactor {t : Real}
    (ht : t ∈ Ioo (-21 / 20 : Real) (-3 / 4)) :
    ContDiffAt Real ∞ minimumCapRayFactor t := by
  have ht0 : t ≠ 0 := by linarith [ht.2]
  have hz : ContDiffAt Real ∞ (fun s : Real => (1 - s ^ 2) / s ^ 2) t :=
    (contDiffAt_const.sub (contDiffAt_id.pow 2)).div (contDiffAt_id.pow 2) (pow_ne_zero _ ht0)
  exact (contDiffAt_const.sub
    ((contDiffAt_minimumCapRayHeight (rayRatio_mem ht)).comp t hz)).div
      contDiffAt_id.neg (neg_ne_zero.mpr ht0)

theorem minimumCapRayFactor_pos {t : Real}
    (ht : t ∈ Ioo (-21 / 20 : Real) (-3 / 4)) :
    0 < minimumCapRayFactor t := by
  apply div_pos
  · linarith [(minimumCapRayHeight_spec (rayRatio_mem ht)).1.2]
  · linarith [ht.2]

theorem minimumCapRayFactor_height {t : Real} (ht : t ≠ 0) :
    minimumCapRayFactor t * t = minimumCapRayHeight ((1 - t ^ 2) / t ^ 2) - 2 := by
  unfold minimumCapRayFactor
  field_simp
  ring

theorem minimumCapRayFactor_projection_sq {t : Real}
    (ht : t ∈ Ioo (-21 / 20 : Real) (-3 / 4)) :
    minimumCapRayFactor t ^ 2 * (1 - t ^ 2) =
      minimumCapSquaredRadius (minimumCapRayHeight ((1 - t ^ 2) / t ^ 2)) := by
  have hs := minimumCapRayHeight_spec (rayRatio_mem ht)
  have ht0 : t ≠ 0 := by linarith [ht.2]
  have hu2 : 2 - minimumCapRayHeight ((1 - t ^ 2) / t ^ 2) ≠ 0 := by linarith [hs.1.2]
  unfold minimumCapRayRatio at hs
  have he := (div_eq_iff (pow_ne_zero 2 hu2)).mp hs.2
  unfold minimumCapRayFactor
  rw [he]
  field_simp

theorem minimumCapRayFactor_eq_cylinder {t : Real}
    (ht : t ∈ Ioo (-9 / 11 : Real) (-3 / 4)) :
    minimumCapRayFactor t = (Real.sqrt (1 - t ^ 2))⁻¹ := by
  have ht' : t ∈ Ioo (-21 / 20 : Real) (-3 / 4) := ⟨by linarith [ht.1], ht.2⟩
  have ht2 : 0 < t ^ 2 := sq_pos_of_neg (by linarith [ht.2])
  have hz : 4 / 9 ≤ (1 - t ^ 2) / t ^ 2 := by
    apply (le_div_iff₀ ht2).mpr
    nlinarith [ht.1, ht.2]
  have hu := minimumCapRayHeight_half_le hz (rayRatio_mem ht').2
  have hsq := minimumCapRayFactor_projection_sq ht'
  rw [minimumCapSquaredRadius_eq_one hu] at hsq
  have hrad : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hroot := Real.sq_sqrt hrad.le
  have hprod : minimumCapRayFactor t * Real.sqrt (1 - t ^ 2) = 1 := by
    have hpos := mul_pos (minimumCapRayFactor_pos ht') (Real.sqrt_pos.mpr hrad)
    nlinarith [sq_nonneg (minimumCapRayFactor t * Real.sqrt (1 - t ^ 2) - 1)]
  rw [← one_div]
  exact (eq_div_iff (Real.sqrt_pos.mpr hrad).ne').mpr hprod

def minimumCapLowerRadius (t : Real) : Real :=
  if t < -4 / 5 then minimumCapRayFactor t else (Real.sqrt (1 - t ^ 2))⁻¹

theorem minimumCapLowerRadius_pos {t : Real} (ht : t ∈ Icc (-1 : Real) 0) :
    0 < minimumCapLowerRadius t := by
  unfold minimumCapLowerRadius
  split_ifs with hl
  · exact minimumCapRayFactor_pos ⟨by linarith [ht.1], by linarith⟩
  · apply inv_pos.mpr
    apply Real.sqrt_pos.mpr
    nlinarith [ht.2]

theorem minimumCapLowerRadius_eq_cylinder {t : Real}
    (ht : -9 / 11 < t) :
    minimumCapLowerRadius t = (Real.sqrt (1 - t ^ 2))⁻¹ := by
  unfold minimumCapLowerRadius
  split_ifs with hl
  · exact minimumCapRayFactor_eq_cylinder ⟨ht, by linarith⟩
  · rfl

theorem contDiffAt_minimumCapLowerRadius {t : Real}
    (ht : t ∈ Ioo (-21 / 20 : Real) 1) :
    ContDiffAt Real ∞ minimumCapLowerRadius t := by
  by_cases hl : t < -4 / 5
  · apply (contDiffAt_minimumCapRayFactor ⟨ht.1, by linarith⟩).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hl] with s hs
    exact if_pos hs
  · have hrad : 0 < 1 - t ^ 2 := by nlinarith [ht.2]
    have hf : ContDiffAt Real ∞ (fun s : Real => (Real.sqrt (1 - s ^ 2))⁻¹) t :=
      ((Real.contDiffAt_sqrt hrad.ne').comp t
        (contDiffAt_const.sub (contDiffAt_id.pow 2))).inv (Real.sqrt_pos.mpr hrad).ne'
    apply hf.congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds (show -9 / 11 < t by linarith)] with s hs
    exact minimumCapLowerRadius_eq_cylinder hs

end Poincare.Manifold.Schoenflies
