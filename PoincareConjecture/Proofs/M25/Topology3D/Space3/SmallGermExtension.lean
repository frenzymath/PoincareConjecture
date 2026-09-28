import PoincareConjecture.Proofs.M25.Topology3D.Space3.CutoffDerivative
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Topology NNReal

namespace PoincareConjecture.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_small_germ_extension (h : E → F) (hh : ContDiff ℝ ∞ h)
    (hh0 : h 0 = 0) (hd0 : fderiv ℝ h 0 = 0)
    {L : ℝ≥0} (hL : 0 < L) {b : ℝ} (hb : 0 < b) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      tsupport g ⊆ ball 0 b ∧ LipschitzWith L g ∧ g =ᶠ[𝓝 0] h := by
  obtain ⟨ρ, hρ, hρc, hρs, hρnear, hρrange⟩ :=
    exists_compact_smooth_cutoff (isCompact_singleton (x := (0 : E)))
      isOpen_ball (singleton_subset_iff.mpr (mem_ball_self zero_lt_one))
  obtain ⟨C, hC⟩ := (hρc.fderiv ℝ).exists_bound_of_continuous
    (hρ.continuous_fderiv (by simp))
  have hC0 : 0 ≤ C := (norm_nonneg (fderiv ℝ ρ 0)).trans (hC 0)
  let ε : ℝ := (L : ℝ) / (1 + C)
  have hε : 0 < ε := div_pos (by exact_mod_cast hL) (by positivity)
  have hnear : {x : E | ‖fderiv ℝ h x‖ < ε} ∈ 𝓝 0 :=
    (isOpen_lt (hh.continuous_fderiv (by simp)).norm continuous_const).mem_nhds
      (by simpa only [mem_ofPred_eq, hd0, norm_zero] using hε)
  obtain ⟨s, hs, hsd⟩ := Metric.mem_nhds_iff.mp hnear
  let r := min s (b / 2)
  have hr : 0 < r := lt_min hs (half_pos hb)
  have hrs : r ≤ s := min_le_left _ _
  have hrb : r < b := (min_le_right s (b / 2)).trans_lt (half_lt_self hb)
  let f : E → F := fun x => r⁻¹ • h (r • x)
  have hf : ContDiff ℝ ∞ f := contDiff_const.smul (hh.comp (contDiff_const.smul contDiff_id))
  have hf0 : f 0 = 0 := by simp [f, hh0]
  have hfd (x : E) (hx : x ∈ ball 0 1) : ‖fderiv ℝ f x‖ ≤ ε := by
    rw [(hasFDerivAt_rescaled h hr.ne' x ((hh.differentiable (by simp)) _)).fderiv]
    have hxs : r • x ∈ ball 0 s := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      exact (mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hx) hr).trans_le (by simpa using hrs)
    exact (hsd hxs).le
  have hρnorm (x : E) : ‖ρ x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hρrange x).1]
    exact (hρrange x).2
  let g₀ : E → F := fun x => ρ x • f x
  have hconstant : (1 + C * 1) * ε = L := by
    dsimp [ε]
    field_simp
  have hg₀ : LipschitzWith L g₀ := by
    have hbound := cutoff_smul_lipschitz ρ hρ f hf hf0 zero_lt_one hC0 hε.le
      hρs hρnorm hC hfd
    have hnn : (⟨(1 + C * 1) * ε, by positivity⟩ : ℝ≥0) = L := NNReal.eq hconstant
    rw [hnn] at hbound
    exact hbound
  let g : E → F := fun x => ρ (r⁻¹ • x) • h x
  have hformula (x : E) : r • g₀ (r⁻¹ • x) = g x := by
    simp [g₀, f, g, smul_smul, hr.ne', mul_comm]
  have hglip : LipschitzWith L g := by
    have hbnd := lipschitz_rescaled g₀ hg₀ (inv_ne_zero hr.ne')
    simpa only [inv_inv, hformula] using hbnd
  have hgs : tsupport g ⊆ closedBall 0 r := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    have hρx : ρ (r⁻¹ • x) ≠ 0 := by
      intro hz
      exact hx (by simp only [g, hz, zero_smul])
    have hnorm := mem_ball_zero_iff.mp (hρs (subset_tsupport ρ hρx))
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr,
      inv_mul_lt_iff₀ hr, mul_one] at hnorm
    exact mem_closedBall_zero_iff.mpr hnorm.le
  refine ⟨g, (hρ.comp (contDiff_const.smul contDiff_id)).smul hh,
    (hρc.comp_smul (inv_ne_zero hr.ne')).smul_right,
    hgs.trans (closedBall_subset_ball hrb), hglip, ?_⟩
  have hρnear' : ∀ᶠ x in 𝓝 (0 : E), ρ x = 1 := by
    simpa only [nhdsSet_singleton] using hρnear
  have hsc : Tendsto (fun x : E => r⁻¹ • x) (𝓝 0) (𝓝 0) := by
    have hsc0 : ContinuousAt (fun x : E => r⁻¹ • x) 0 :=
      (continuous_const.smul continuous_id).continuousAt
    simpa only [ContinuousAt, smul_zero] using hsc0
  filter_upwards [hsc.eventually hρnear'] with x hx
  simp only [g, hx, one_smul]

end PoincareConjecture.M25.Topology3D
