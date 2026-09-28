import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Topology.Order.Compact









noncomputable section
set_option autoImplicit false

open Set Function
open scoped ContDiff

namespace PoincareConjecture

theorem exists_half_neck_profile :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∀ σ : ℝ, |σ| = 1 →
      ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧
        support φ ⊆ Icc (-(3 / 4) * ε⁻¹) ((3 / 4) * ε⁻¹) ∧
        φ 0 = 0 ∧ φ (σ / (2 * ε)) = 1 ∧
        ∀ s, |deriv φ s| ≤ C * ε := by
  let f : ContDiffBump (0 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  have hf_smooth : ContDiff ℝ ∞ (f : ℝ → ℝ) := f.contDiff
  have hf : Continuous (fun s : ℝ => ‖deriv (f : ℝ → ℝ) s‖) :=
    (hf_smooth.continuous_deriv (by simp)).norm
  obtain ⟨B, hB⟩ := hf.bddAbove_range_of_hasCompactSupport f.hasCompactSupport.deriv.norm
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro ε hε σ hσ
  let φ : ℝ → ℝ := fun s => f (ε * s - σ / 2)
  have hσle : |σ / 2| = 1 / 2 := by rw [abs_div, hσ]; norm_num
  have hφsupport : support φ ⊆ Icc (-(3 / 4) * ε⁻¹) ((3 / 4) * ε⁻¹) := by
    intro s hs
    have hsf : ε * s - σ / 2 ∈ support (f : ℝ → ℝ) := hs
    rw [f.support_eq] at hsf
    have hsmall : |ε * s - σ / 2| < 1 / 4 := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hsf
    have habs : |ε * s| ≤ 3 / 4 := by
      have h := abs_add_le (ε * s - σ / 2) (σ / 2)
      rw [sub_add_cancel, hσle] at h
      linarith
    rw [abs_mul, abs_of_pos hε] at habs
    have hsa : |s| ≤ (3 / 4) * ε⁻¹ := by
      apply (le_div_iff₀ hε).mpr
      simpa only [mul_comm] using habs
    exact ⟨by linarith [neg_abs_le s], (le_abs_self s).trans hsa⟩
  refine ⟨φ, f.contDiff.comp (by fun_prop), hφsupport, ?_, ?_, ?_⟩
  · apply f.zero_of_le_dist
    change (1 / 4 : ℝ) ≤ dist (ε * 0 - σ / 2) 0
    rw [Real.dist_eq, mul_zero, zero_sub, sub_zero, abs_neg, hσle]
    norm_num
  · have heq : ε * (σ / (2 * ε)) - σ / 2 = 0 := by
      field_simp
      ring
    change f (ε * (σ / (2 * ε)) - σ / 2) = 1
    rw [heq]
    exact f.one_of_mem_closedBall (by norm_num [f])
  · intro s
    have hd : deriv φ s = deriv (f : ℝ → ℝ) (ε * s - σ / 2) * ε := by
      simpa only [φ, Function.comp_def, mul_one, id_eq] using
        ((hf_smooth.differentiable (by simp) _).hasDerivAt.comp s
          (((hasDerivAt_id s).const_mul ε).sub_const (σ / 2))).deriv
    rw [hd, abs_mul, abs_of_pos hε]
    apply mul_le_mul_of_nonneg_right _ hε.le
    exact (show |deriv (f : ℝ → ℝ) (ε * s - σ / 2)| ≤ B from
      hB (mem_range_self _)).trans (le_max_left _ _)

def neckDepthConstant : ℝ := exists_half_neck_profile.choose

theorem neckDepthConstant_pos : 0 < neckDepthConstant :=
  exists_half_neck_profile.choose_spec.1


def neckSeparationThreshold : ℝ := min (1 / 4) (1 / (8 * Real.pi * neckDepthConstant))

theorem neckSeparationThreshold_pos : 0 < neckSeparationThreshold := by
  have h := neckDepthConstant_pos
  unfold neckSeparationThreshold
  positivity

theorem neckSeparationThreshold_lt_half : neckSeparationThreshold < 1 / 2 :=
  lt_of_le_of_lt (min_le_left _ _) (by norm_num)

end PoincareConjecture
