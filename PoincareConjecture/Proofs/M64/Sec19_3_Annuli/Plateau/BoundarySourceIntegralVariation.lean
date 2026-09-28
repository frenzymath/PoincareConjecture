import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundarySourceCoefficients
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

theorem m64HorizontalSource_integral_firstVariation
    (tau : ℝ → ℝ ≃ₜ ℝ) {theta : ℝ → ℝ} (htheta : ContDiff ℝ ∞ theta)
    (hperiod : Function.Periodic theta curvePeriod)
    (hvar : ∀ᶠ t : ℝ in 𝓝 0, ∀ x, tau t x = x + t * theta x)
    {f g : LoopPlane → ℝ} (hf : Integrable f mu) (hg : Integrable g mu) (r : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ p in S,
      (r * (1 + t * deriv theta ((tau t).symm (p 0))) * f p +
        r⁻¹ * (1 + t * deriv theta ((tau t).symm (p 0)))⁻¹ * g p) / 2)
      (∫ p in S, deriv theta (p 0) * (r * f p - r⁻¹ * g p) / 2) 0 := by
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hc := hperiod.compact_of_continuous hP.ne' htheta.continuous
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn continuousOn_id
  have hb (x : ℝ) : |theta x| ≤ B := hB _ (mem_range_self x)
  have hdperiod : Function.Periodic (deriv theta) curvePeriod := by
    intro x
    have hfun : (fun y => theta (y + curvePeriod)) = theta := funext hperiod
    have hh := congrArg (fun f : ℝ → ℝ => deriv f x) hfun
    simpa only [deriv_comp_add_const] using hh
  have hdc := htheta.continuous_deriv (by simp)
  have hdcpt := hdperiod.compact_of_continuous hP.ne' hdc
  obtain ⟨C0, hC0⟩ := hdcpt.exists_bound_of_continuousOn continuousOn_id
  let C := max C0 0
  have hC : 0 ≤ C := le_max_right _ _
  let a := fun (t : ℝ) (p : LoopPlane) => deriv theta ((tau t).symm (p 0))
  let q := fun (t : ℝ) (p : LoopPlane) => 1 + t * a t p
  let J := fun (t : ℝ) (p : LoopPlane) => (r * q t p * f p + r⁻¹ * (q t p)⁻¹ * g p) / 2
  let V := fun (t : ℝ) (p : LoopPlane) => a t p * (r * f p - r⁻¹ * g p / q t p) / 2
  let v := fun p : LoopPlane => deriv theta (p 0) * (r * f p - r⁻¹ * g p) / 2
  let bound := fun p : LoopPlane => (C / 2) * (|r| * |f p| + 2 * |r⁻¹| * |g p|)
  have ha (t : ℝ) (p : LoopPlane) : |a t p| ≤ C :=
    (hC0 _ (mem_range_self _)).trans (le_max_left _ _)
  have ham (t : ℝ) : AEStronglyMeasurable (a t) mu :=
    (hdc.comp ((tau t).symm.continuous.comp
      (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).continuous)).aestronglyMeasurable
  have hqm (t : ℝ) : AEStronglyMeasurable (q t) mu :=
    aestronglyMeasurable_const.add ((ham t).const_mul t)
  have hVm (t : ℝ) : AEStronglyMeasurable (V t) mu :=
    ((ham t).mul ((hf.aestronglyMeasurable.const_mul r).sub
      ((hg.aestronglyMeasurable.const_mul r⁻¹).div₀ (hqm t)))).div₀
        aestronglyMeasurable_const
  have hbound : Integrable bound mu :=
    (((hf.norm.const_mul |r|).add (hg.norm.const_mul (2 * |r⁻¹|))).const_mul (C / 2))
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| * C < 1 / 2 := by
    have hc : ContinuousAt (fun t : ℝ => |t| * C) 0 := continuous_abs.continuousAt.mul_const C
    exact hc.eventually (gt_mem_nhds (by norm_num : |(0 : ℝ)| * C < 1 / 2))
  have hqpos {t : ℝ} (ht : |t| * C < 1 / 2) (p : LoopPlane) : 1 / 2 < q t p := by
    have hprod := mul_le_mul_of_nonneg_left (ha t p) (abs_nonneg t)
    rw [← abs_mul] at hprod
    have hlo := (abs_le.mp hprod).1
    dsimp only [q]
    linarith
  have hVbound {t : ℝ} (ht : |t| * C < 1 / 2) (p : LoopPlane) :
      ‖V t p‖ ≤ bound p := by
    have hq := hqpos ht p
    have hqp : 0 < q t p := lt_trans (by norm_num) hq
    have hinv : (q t p)⁻¹ ≤ 2 := by
      rw [inv_le_iff_one_le_mul₀ hqp]
      linarith
    have hterm : |r⁻¹ * g p / q t p| ≤ 2 * |r⁻¹| * |g p| := by
      rw [abs_div, abs_mul, abs_of_pos hqp, div_eq_mul_inv]
      nlinarith [mul_le_mul_of_nonneg_left hinv (mul_nonneg (abs_nonneg r⁻¹) (abs_nonneg (g p)))]
    have hsub : |r * f p - r⁻¹ * g p / q t p| ≤ |r| * |f p| + 2 * |r⁻¹| * |g p| :=
      (abs_sub _ _).trans (by rw [abs_mul]; linarith)
    change |a t p * (r * f p - r⁻¹ * g p / q t p) / 2| ≤ _
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hm := mul_le_mul (ha t p) hsub (abs_nonneg _) hC
    dsimp only [bound]
    nlinarith
  have hVI {t : ℝ} (ht : |t| * C < 1 / 2) : Integrable (V t) mu :=
    hbound.mono' (hVm t) (Eventually.of_forall (hVbound ht))
  have hlim (p : LoopPlane) : Tendsto (fun t => V t p) (𝓝 0) (𝓝 (v p)) := by
    have hat : Tendsto (fun t => a t p) (𝓝 0) (𝓝 (deriv theta (p 0))) :=
      hdc.continuousAt.tendsto.comp (m64HorizontalSourceInverse_tendsto tau theta hb hvar (p 0))
    have hqt : Tendsto (fun t => q t p) (𝓝 0) (𝓝 1) := by
      simpa only [zero_mul, add_zero, id_eq, q] using
        tendsto_const_nhds.add (tendsto_id.mul hat)
    have hf0 : Tendsto (fun _ : ℝ => r * f p) (𝓝 0) (𝓝 (r * f p)) := tendsto_const_nhds
    have hg0 : Tendsto (fun _ : ℝ => r⁻¹ * g p) (𝓝 0) (𝓝 (r⁻¹ * g p)) :=
      tendsto_const_nhds
    have hh := (hat.mul (hf0.sub (hg0.div hqt one_ne_zero))).div_const (2 : ℝ)
    simpa only [div_one, V, v, Pi.div_apply] using hh
  have hIlim : Tendsto (fun t => ∫ p in S, V t p) (𝓝 0) (𝓝 (∫ p in S, v p)) :=
    tendsto_integral_filter_of_dominated_convergence bound
      (Eventually.of_forall hVm)
      (hsmall.mono fun t ht => Eventually.of_forall (hVbound ht)) hbound
      (Eventually.of_forall hlim)
  have hJ0 : Integrable (J 0) mu := by
    simpa only [J, q, zero_mul, add_zero, inv_one, mul_one, Pi.add_apply] using
      ((hf.const_mul r).add (hg.const_mul r⁻¹)).div_const 2
  have hpoint {t : ℝ} (ht : |t| * C < 1 / 2) (p : LoopPlane) :
      J t p = J 0 p + t * V t p := by
    have hne : q t p ≠ 0 := (lt_trans (by norm_num) (hqpos ht p)).ne'
    dsimp only [J, V]
    simp only [q, zero_mul, add_zero, inv_one, mul_one]
    dsimp only [q] at hne
    field_simp [hne]
    ring
  have hJI {t : ℝ} (ht : |t| * C < 1 / 2) : Integrable (J t) mu :=
    (hJ0.add ((hVI ht).const_mul t)).congr (Eventually.of_forall fun p => (hpoint ht p).symm)
  change HasDerivAt (fun t => ∫ p in S, J t p) (∫ p in S, v p) 0
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply (hIlim.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht ht0
  have hne : t ≠ 0 := ht0
  have hsplit : (∫ p in S, J t p) = (∫ p in S, J 0 p) + t * ∫ p in S, V t p := by
    simp_rw [hpoint ht]
    rw [integral_add hJ0 ((hVI ht).const_mul t), integral_const_mul]
  simp only [slope, sub_zero, vsub_eq_sub, smul_eq_mul, hsplit, add_sub_cancel_left]
  rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end PoincareConjecture
