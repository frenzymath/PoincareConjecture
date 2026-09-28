import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul












set_option autoImplicit false

open Set Metric
open scoped ContDiff NNReal

namespace PoincareConjecture.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem hasFDerivAt_rescaled (f : E → F) {r : ℝ} (hr : r ≠ 0) (x : E)
    (hf : DifferentiableAt ℝ f (r • x)) :
    HasFDerivAt (fun y => r⁻¹ • f (r • y)) (fderiv ℝ f (r • x)) x := by
  have h := (hf.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul r)).const_smul r⁻¹
  apply h.congr_fderiv
  ext y
  simp [smul_smul, hr]



theorem cutoff_smul_fderiv_bound (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hf0 : f 0 = 0)
    {R C ε : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hs : tsupport ρ ⊆ ball 0 R) (hρnorm : ∀ x, ‖ρ x‖ ≤ 1)
    (hρderiv : ∀ x, ‖fderiv ℝ ρ x‖ ≤ C)
    (hfderiv : ∀ x ∈ ball 0 R, ‖fderiv ℝ f x‖ ≤ ε) (x : E) :
    ‖fderiv ℝ (fun y => ρ y • f y) x‖ ≤ (1 + C * R) * ε := by
  by_cases hx : x ∈ tsupport ρ
  · have hxR := hs hx
    have hfval : ‖f x‖ ≤ ε * R := by
      have h := (convex_ball (0 : E) R).norm_image_sub_le_of_norm_fderiv_le
        (fun y _ => (hf.differentiable (by simp)) y) hfderiv
        (mem_ball_self hR) hxR
      rw [hf0, sub_zero, sub_zero] at h
      exact h.trans (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hxR).le hε)
    rw [fderiv_fun_smul ((hρ.differentiable (by simp)) x)
      ((hf.differentiable (by simp)) x)]
    calc
      ‖ρ x • fderiv ℝ f x + (fderiv ℝ ρ x).smulRight (f x)‖ ≤
          ‖ρ x • fderiv ℝ f x‖ + ‖(fderiv ℝ ρ x).smulRight (f x)‖ := norm_add_le _ _
      _ = ‖ρ x‖ * ‖fderiv ℝ f x‖ + ‖fderiv ℝ ρ x‖ * ‖f x‖ := by
        rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
      _ ≤ 1 * ε + C * (ε * R) := add_le_add
        (mul_le_mul (hρnorm x) (hfderiv x hxR) (norm_nonneg _) zero_le_one)
        (mul_le_mul (hρderiv x) hfval (norm_nonneg _) hC)
      _ = (1 + C * R) * ε := by ring
  · have hg : x ∉ tsupport (fun y => ρ y • f y) :=
      fun h => hx ((tsupport_smul_subset_left ρ f) h)
    rw [fderiv_of_notMem_tsupport ℝ hg, norm_zero]
    positivity


theorem cutoff_smul_lipschitz (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hf0 : f 0 = 0)
    {R C ε : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hs : tsupport ρ ⊆ ball 0 R) (hρnorm : ∀ x, ‖ρ x‖ ≤ 1)
    (hρderiv : ∀ x, ‖fderiv ℝ ρ x‖ ≤ C)
    (hfderiv : ∀ x ∈ ball 0 R, ‖fderiv ℝ f x‖ ≤ ε) :
    LipschitzWith ⟨(1 + C * R) * ε, by positivity⟩ (fun x => ρ x • f x) := by
  apply lipschitzWith_of_nnnorm_fderiv_le ((hρ.smul hf).differentiable (by simp))
  intro x
  exact_mod_cast cutoff_smul_fderiv_bound ρ hρ f hf hf0 hR hC hε
    hs hρnorm hρderiv hfderiv x



theorem lipschitz_rescaled (f : E → F) {L : ℝ≥0} (hf : LipschitzWith L f)
    {r : ℝ} (hr : r ≠ 0) : LipschitzWith L (fun x => r⁻¹ • f (r • x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← smul_sub, norm_smul]
  calc
    ‖r⁻¹‖ * ‖f (r • x) - f (r • y)‖ ≤ ‖r⁻¹‖ * (L * ‖r • x - r • y‖) :=
      mul_le_mul_of_nonneg_left (hf.norm_sub_le _ _) (norm_nonneg _)
    _ = L * dist x y := by
      rw [← smul_sub, norm_smul, norm_inv, dist_eq_norm]
      have hn : ‖r‖ ≠ 0 := norm_ne_zero_iff.mpr hr
      field_simp

end PoincareConjecture.M25.Topology3D
