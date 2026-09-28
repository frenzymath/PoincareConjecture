import PoincareConjecture.Proofs.M47.NoncollapseHorizonBalls

set_option autoImplicit false

open Set Filter
open scoped Topology ENNReal

namespace PoincareConjecture.Proofs.M47

theorem exists_horizon_earlier_parameter {a T r q C : ℝ}
    (haT : a < T) (hr : 0 < r) (hq : 0 < q) (hqr : q < r) (hC : 1 < C) :
    ∃ s ∈ Ioo (-r ^ 2) 0, a ≤ T + s ∧ -r ^ 2 ≤ s - q ^ 2 ∧
      Real.exp (6 * r⁻¹ ^ 2 * (-s)) ≤ C ^ 2 := by
  let lower := max (a - T) (q ^ 2 - r ^ 2)
  have hgap : q ^ 2 < r ^ 2 := sq_lt_sq₀ hq.le hr.le |>.mpr hqr
  have hlower : lower < 0 := max_lt (sub_neg.mpr haT) (sub_neg.mpr hgap)
  have hCsq : (1 : ℝ) < C ^ 2 := by nlinarith only [hC, sq_nonneg (C - 1)]
  have hE : Continuous (fun s : ℝ => Real.exp (6 * r⁻¹ ^ 2 * (-s))) := by fun_prop
  have hsmall : ∀ᶠ s in 𝓝 (0 : ℝ), Real.exp (6 * r⁻¹ ^ 2 * (-s)) < C ^ 2 :=
    hE.continuousAt.eventually (Iio_mem_nhds (by simpa only [neg_zero, mul_zero,
      Real.exp_zero] using hCsq))
  have hlowerNear : ∀ᶠ s in 𝓝 (0 : ℝ), lower < s := Ioi_mem_nhds hlower
  have hevent : ∀ᶠ s in 𝓝[<] (0 : ℝ),
      lower < s ∧ s < 0 ∧ Real.exp (6 * r⁻¹ ^ 2 * (-s)) < C ^ 2 := by
    filter_upwards [hlowerNear.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds] with s hlo hs hbound
    exact ⟨hlo, hs, hbound⟩
  obtain ⟨s, hlo, hs, hbound⟩ := hevent.exists
  have hstart : a - T < s := (le_max_left _ _).trans_lt hlo
  have htime : q ^ 2 - r ^ 2 < s := (le_max_right _ _).trans_lt hlo
  exact ⟨s, ⟨by linarith only [htime, sq_nonneg q], hs⟩,
    by linarith only [hstart], by linarith only [htime], hbound.le⟩

theorem horizon_volume_of_contracted_densities {kappa r : ℝ} {V : ℝ≥0∞}
    (hvolume : ∀ theta ∈ Ioo (0 : ℝ) 1,
      ENNReal.ofReal (kappa * theta ^ 9 * r ^ 3) ≤ V) :
    ENNReal.ofReal (kappa * r ^ 3) ≤ V := by
  have hcontinuous : Continuous (fun theta : ℝ =>
      ENNReal.ofReal (kappa * theta ^ 9 * r ^ 3)) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  have hlim : Tendsto (fun theta : ℝ => ENNReal.ofReal (kappa * theta ^ 9 * r ^ 3))
      (𝓝[<] 1) (𝓝 (ENNReal.ofReal (kappa * r ^ 3))) := by
    simpa only [one_pow, mul_one] using
      (hcontinuous.continuousAt (x := (1 : ℝ))).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  have hpositive : ∀ᶠ theta in 𝓝 (1 : ℝ), 0 < theta := Ioi_mem_nhds zero_lt_one
  filter_upwards [hpositive.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with theta htheta htheta1
  exact hvolume theta ⟨htheta, htheta1⟩

end PoincareConjecture.Proofs.M47
