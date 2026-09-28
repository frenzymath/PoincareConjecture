import PoincareConjecture.Proofs.M65.Mathlib.Plateau.BeltramiMap
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.CocompactMap
import Mathlib.Topology.Maps.Proper.CompactlyGenerated










set_option autoImplicit false

noncomputable section

open Filter Set Metric
open scoped Topology ContDiff SchwartzMap ComplexConjugate

namespace Complex





theorem isProperMap_of_fderiv_tendsto_id (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hlim : Tendsto (fderiv ℝ f) (cocompact ℂ) (𝓝 (ContinuousLinearMap.id ℝ ℂ))) :
    IsProperMap f := by
  have hnear : ∀ᶠ z in cocompact ℂ,
      ‖fderiv ℝ f z - ContinuousLinearMap.id ℝ ℂ‖ < (1 / 2 : ℝ) := by
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp hlim) (1 / 2) (by norm_num)
  obtain ⟨r, hr⟩ := closedBall_compl_subset_of_mem_cocompact hnear (0 : ℂ)
  let R := max (r + 1) 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hrR : r < R := by dsimp [R]; linarith [le_max_left (r + 1) 1]
  have hbound (z : ℂ) (hz : R ≤ ‖z‖) :
      ‖fderiv ℝ f z - ContinuousLinearMap.id ℝ ℂ‖ ≤ (1 / 2 : ℝ) := by
    exact (hr (by
      simpa only [Set.mem_compl_iff, mem_closedBall_zero_iff, not_le]
        using hrR.trans_le hz)).le
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    (hf.continuous.sub continuous_id).continuousOn
  have herror (z : ℂ) (hz : R < ‖z‖) : ‖f z - z‖ ≤ (1 / 2 : ℝ) * ‖z‖ + C := by
    have hz0 : 0 < ‖z‖ := hR.trans hz
    let a := R / ‖z‖
    have ha0 : 0 ≤ a := div_nonneg hR.le hz0.le
    have ha1 : a ≤ 1 := (div_le_one hz0).mpr hz.le
    have hanorm : a * ‖z‖ = R := div_mul_cancel₀ R hz0.ne'
    let p : ℝ → ℂ := fun t => f (t • z) - t • z
    let p' : ℝ → ℂ := fun t => (fderiv ℝ f (t • z) - ContinuousLinearMap.id ℝ ℂ) z
    have hpd (t : ℝ) : HasDerivAt p (p' t) t := by
      have hline : HasDerivAt (fun s : ℝ => s • z) z t := by
        simpa only [one_smul, id_eq] using! (hasDerivAt_id t).smul_const z
      have hcomp := (hf.differentiable (by simp) (t • z)).hasFDerivAt.comp_hasDerivAt t hline
      convert! hcomp.sub hline using 1
    have hpb (t : ℝ) (ht : t ∈ Ico a 1) : ‖p' t‖ ≤ (1 / 2 : ℝ) * ‖z‖ := by
      have ht0 : 0 ≤ t := ha0.trans ht.1
      have htnorm : R ≤ ‖t • z‖ := by
        rw [norm_smul, Real.norm_of_nonneg ht0]
        rw [← hanorm]
        exact mul_le_mul_of_nonneg_right ht.1 hz0.le
      exact ((fderiv ℝ f (t • z) - ContinuousLinearMap.id ℝ ℂ).le_opNorm z).trans
        (mul_le_mul_of_nonneg_right (hbound _ htnorm) hz0.le)
    have hseg := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t _ => (hpd t).hasDerivWithinAt) hpb 1 ⟨ha1, le_rfl⟩
    have hseg' : ‖p 1 - p a‖ ≤ (1 / 2 : ℝ) * ‖z‖ :=
      hseg.trans (mul_le_of_le_one_right (by positivity) (by linarith))
    have hsmall : ‖p a‖ ≤ C := hC (a • z) (by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg ha0, hanorm])
    calc
      _ = ‖p 1‖ := by simp only [p, one_smul]
      _ ≤ ‖p 1 - p a‖ + ‖p a‖ := norm_le_norm_sub_add _ _
      _ ≤ _ := _root_.add_le_add hseg' hsmall
  apply isProperMap_iff_tendsto_cocompact.mpr
  refine ⟨hf.continuous, tendsto_cocompact_cocompact_of_norm (fun B => ?_)⟩
  refine ⟨max R (2 * (B + C)), fun z hz => ?_⟩
  have hzR : R < ‖z‖ := (le_max_left _ _).trans_lt hz
  have hzB : 2 * (B + C) < ‖z‖ := (le_max_right _ _).trans_lt hz
  have htri : ‖z‖ ≤ ‖f z‖ + ‖f z - z‖ := by
    calc
      _ = ‖f z - (f z - z)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  linarith [herror z hzR]




theorem exists_proper_nondegenerate_beltrami_map (μ : 𝓢(ℂ, ℂ))
    (hμ : HasCompactSupport (μ : ℂ → ℂ)) {k : ℝ} (hk : k < 1)
    (hbound : ∀ z, ‖μ z‖ ≤ k) :
    ∃ f : ℂ → ℂ, ContDiff ℝ ∞ f ∧ IsProperMap f ∧
      Tendsto (fderiv ℝ f) (cocompact ℂ) (𝓝 (ContinuousLinearMap.id ℝ ℂ)) ∧
      (∀ z, Function.Bijective (fderiv ℝ f z)) ∧ ∀ z,
        fderiv ℝ f z 1 + I * fderiv ℝ f z I =
          μ z * (fderiv ℝ f z 1 - I * fderiv ℝ f z I) := by
  obtain ⟨f, w, hf, _, hwinf, _, hformula, hbij⟩ :=
    exists_smooth_nondegenerate_beltrami_map μ hμ hk hbound
  have hD : fderiv ℝ f = fun z => w z • ContinuousLinearMap.id ℝ ℂ +
      (μ z * w z) • (conjCLE : ℂ →L[ℝ] ℂ) := by
    funext z
    ext v
    rw [hformula]
    change _ = w z * v + (μ z * w z) * conj v
    ring
  have hlim : Tendsto (fderiv ℝ f) (cocompact ℂ)
      (𝓝 (ContinuousLinearMap.id ℝ ℂ)) := by
    rw [hD]
    have hμinf : Tendsto (μ : ℂ → ℂ) (cocompact ℂ) (𝓝 0) := hμ.is_zero_at_infty
    have hlimit := (hwinf.smul_const (ContinuousLinearMap.id ℝ ℂ)).add
      ((hμinf.mul hwinf).smul_const (conjCLE : ℂ →L[ℝ] ℂ))
    convert! hlimit using 1
    congr 1
    ext v
    simp
  refine ⟨f, hf, isProperMap_of_fderiv_tendsto_id f hf hlim, hlim, hbij, fun z => ?_⟩
  simp only [hformula, map_one, conj_I]
  ring_nf
  simp only [I_sq]
  ring

end Complex
