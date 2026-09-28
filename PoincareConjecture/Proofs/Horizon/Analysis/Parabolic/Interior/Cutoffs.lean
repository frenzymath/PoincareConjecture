import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Localization
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open Filter Set
open scoped ContDiff Topology

namespace Poincare.Parabolic.Interior

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def rescaledCutoff (χ : E → ℝ) (center : E) (r : ℝ) (x : E) : ℝ :=
  χ (r⁻¹ • (x - center))

theorem contDiff_rescaledCutoff {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (center : E) (r : ℝ) : ContDiff ℝ ∞ (rescaledCutoff χ center r) := by
  exact hχ.comp ((contDiff_id.sub contDiff_const).const_smul _)

theorem fderiv_rescaledCutoff {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (center : E) (r : ℝ) (x : E) :
    fderiv ℝ (rescaledCutoff χ center r) x =
      r⁻¹ • fderiv ℝ χ (r⁻¹ • (x - center)) := by
  have h := ((hχ.differentiable (by simp)) _).hasFDerivAt.comp x
    (((hasFDerivAt_id x).sub_const center).const_smul r⁻¹)
  change HasFDerivAt (rescaledCutoff χ center r) _ x at h
  rw [h.fderiv]
  ext v
  simp

theorem fderiv_fderiv_rescaledCutoff_apply {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (center : E) (r : ℝ) (x v w : E) :
    fderiv ℝ (fderiv ℝ (rescaledCutoff χ center r)) x v w =
      r⁻¹ * r⁻¹ * fderiv ℝ (fderiv ℝ χ) (r⁻¹ • (x - center)) v w := by
  have hdχ := (hχ.fderiv_right (by simp : ∞ + 1 ≤ (∞ : WithTop ℕ∞))).differentiable (by simp)
  have h := ((hdχ _).hasFDerivAt.comp x
    (((hasFDerivAt_id x).sub_const center).const_smul r⁻¹)).const_smul r⁻¹
  have heq : fderiv ℝ (rescaledCutoff χ center r) =
      fun y => r⁻¹ • fderiv ℝ χ (r⁻¹ • (y - center)) :=
    funext (fderiv_rescaledCutoff hχ center r)
  change HasFDerivAt (fun y => r⁻¹ • fderiv ℝ χ (r⁻¹ • (y - center))) _ x at h
  rw [heq, h.fderiv]
  simp [mul_assoc]

theorem norm_fderiv_rescaledCutoff_le {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {C r : ℝ} (hr : 0 < r) (hb : ∀ x, ‖fderiv ℝ χ x‖ ≤ C)
    (center x : E) : ‖fderiv ℝ (rescaledCutoff χ center r) x‖ ≤ C / r := by
  rw [fderiv_rescaledCutoff hχ, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left (hb (r⁻¹ • (x - center))) (inv_nonneg.mpr hr.le)

theorem norm_fderiv_fderiv_rescaledCutoff_le {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {C r : ℝ} (hC : 0 ≤ C) (hr : 0 < r) (hb : ∀ x, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ C)
    (center x : E) : ‖fderiv ℝ (fderiv ℝ (rescaledCutoff χ center r)) x‖ ≤ C / r ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [fderiv_fderiv_rescaledCutoff_apply hχ, norm_mul, norm_mul,
    Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  calc
    _ ≤ (r⁻¹ * r⁻¹) * ((‖fderiv ℝ (fderiv ℝ χ) (r⁻¹ • (x - center))‖ * ‖v‖) * ‖w‖) := by
      gcongr
      exact ContinuousLinearMap.le_opNorm₂ _ _ _
    _ ≤ (r⁻¹ * r⁻¹) * ((C * ‖v‖) * ‖w‖) := by gcongr; exact hb _
    _ = _ := by simp [div_eq_mul_inv, pow_two]; ring

section FiniteDimension

variable [FiniteDimensional ℝ E] [HasContDiffBump E]

def unitSpatialBump : ContDiffBump (0 : E) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem exists_unit_cutoff_derivative_bounds :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      (∀ x : E, ‖fderiv ℝ (unitSpatialBump (E := E) : E → ℝ) x‖ ≤ C₁) ∧
      (∀ x : E, ‖fderiv ℝ (fderiv ℝ (unitSpatialBump (E := E) : E → ℝ)) x‖ ≤ C₂) := by
  have hχ : ContDiff ℝ ∞ (unitSpatialBump (E := E) : E → ℝ) := unitSpatialBump.contDiff
  have hc : HasCompactSupport (unitSpatialBump (E := E) : E → ℝ) := unitSpatialBump.hasCompactSupport
  obtain ⟨C₁, h₁⟩ := (hc.fderiv ℝ).exists_bound_of_continuous (hχ.continuous_fderiv (by simp))
  obtain ⟨C₂, h₂⟩ := ((hc.fderiv ℝ).fderiv ℝ).exists_bound_of_continuous
    ((hχ.fderiv_right (by simp : ∞ + 1 ≤ (∞ : WithTop ℕ∞))).continuous_fderiv (by simp))
  exact ⟨max 0 C₁, max 0 C₂, le_max_left _ _, le_max_left _ _,
    fun x => (h₁ x).trans (le_max_right _ _), fun x => (h₂ x).trans (le_max_right _ _)⟩

omit [FiniteDimensional ℝ E] in
theorem rescaled_unit_cutoff_mem_Icc (center : E) (r : ℝ) (x : E) :
    rescaledCutoff (unitSpatialBump (E := E)) center r x ∈ Icc (0 : ℝ) 1 :=
  ⟨unitSpatialBump.nonneg, unitSpatialBump.le_one⟩

omit [FiniteDimensional ℝ E] in
theorem rescaled_unit_cutoff_eq_zero {r : ℝ} (hr : 0 < r) (center x : E)
    (hx : r ≤ ‖x - center‖) : rescaledCutoff (unitSpatialBump (E := E)) center r x = 0 := by
  apply unitSpatialBump.zero_of_le_dist
  change 1 ≤ dist (r⁻¹ • (x - center)) 0
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  simpa only [div_eq_inv_mul] using (one_le_div hr).mpr hx

omit [FiniteDimensional ℝ E] in
theorem rescaled_unit_cutoff_eventuallyEq_one {r : ℝ} (hr : 0 < r)
    (center : E) {x : E} (hx : ‖x - center‖ < r / 2) :
    rescaledCutoff (unitSpatialBump (E := E)) center r =ᶠ[𝓝 x] fun _ => 1 := by
  have hmem : r⁻¹ • (x - center) ∈ Metric.ball (0 : E) (unitSpatialBump (E := E)).rIn := by
    change dist (r⁻¹ • (x - center)) 0 < (1 / 2 : ℝ)
    rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    rw [← div_eq_inv_mul, div_lt_iff₀ hr]
    linarith
  exact unitSpatialBump.eventuallyEq_one_of_mem_ball hmem |>.comp_tendsto
    (((continuous_id.sub continuous_const).const_smul r⁻¹).tendsto x)

omit [FiniteDimensional ℝ E] in
theorem tsupport_rescaled_unit_cutoff_subset {r : ℝ} (hr : 0 < r) (center : E) :
    tsupport (rescaledCutoff (unitSpatialBump (E := E)) center r) ⊆
      Metric.closedBall center r := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact le_of_lt (lt_of_not_ge fun h => hx (rescaled_unit_cutoff_eq_zero hr center x h))

theorem hasCompactSupport_rescaled_unit_cutoff {r : ℝ} (hr : 0 < r) (center : E) :
    HasCompactSupport (rescaledCutoff (unitSpatialBump (E := E)) center r) :=
  (isCompact_closedBall center r).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_rescaled_unit_cutoff_subset hr center)

end FiniteDimension

def timeCutoff (T s : ℝ) : ℝ :=
  rescaledCutoff (unitSpatialBump (E := ℝ)) T T s

theorem contDiff_timeCutoff (T : ℝ) : ContDiff ℝ ∞ (timeCutoff T) :=
  contDiff_rescaledCutoff unitSpatialBump.contDiff T T

theorem timeCutoff_mem_Icc (T s : ℝ) : timeCutoff T s ∈ Icc (0 : ℝ) 1 :=
  rescaled_unit_cutoff_mem_Icc T T s

theorem timeCutoff_zero {T : ℝ} (hT : 0 < T) : timeCutoff T 0 = 0 := by
  apply rescaled_unit_cutoff_eq_zero hT
  simp [Real.norm_eq_abs, abs_of_pos hT]

theorem timeCutoff_eventuallyEq_one {T s : ℝ} (hT : 0 < T)
    (hs : T / 2 < s) (hsT : s ≤ T) : timeCutoff T =ᶠ[𝓝 s] fun _ => 1 := by
  apply rescaled_unit_cutoff_eventuallyEq_one hT
  rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hsT)]
  linarith

theorem deriv_timeCutoff_eq_zero {T s : ℝ} (hT : 0 < T)
    (hs : T / 2 < s) (hsT : s ≤ T) : deriv (timeCutoff T) s = 0 := by
  rw [(timeCutoff_eventuallyEq_one hT hs hsT).deriv_eq, deriv_const]

theorem norm_deriv_timeCutoff_le {C T : ℝ} (hT : 0 < T)
    (hC : ∀ x : ℝ, ‖fderiv ℝ (unitSpatialBump (E := ℝ) : ℝ → ℝ) x‖ ≤ C)
    (s : ℝ) : ‖deriv (timeCutoff T) s‖ ≤ C / T := by
  rw [norm_deriv_eq_norm_fderiv]
  exact norm_fderiv_rescaledCutoff_le unitSpatialBump.contDiff hT hC T s
end Poincare.Parabolic.Interior
