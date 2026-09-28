import PoincareConjecture.Proofs.Horizon.Analysis.Convex.Semiconcavity.Derivative
import Mathlib.Analysis.Calculus.ContDiff.Deriv



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Metric
open scoped Topology ContDiff

namespace Poincare.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem eventually_quadratic_bounds_of_fderiv2
    {f : E → ℝ} (hf : ContDiffAt ℝ ∞ f 0) (hzero : fderiv ℝ f 0 = 0)
    {a ε : ℝ} (hhess : ∀ v, fderiv ℝ (fderiv ℝ f) 0 v v = a * ‖v‖ ^ 2)
    (hε : 0 < ε) :
    ∀ᶠ v in 𝓝 (0 : E),
      (a - ε) * ‖v‖ ^ 2 / 2 ≤ f v - f 0 ∧
        f v - f 0 ≤ (a + ε) * ‖v‖ ^ 2 / 2 := by
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  have hsecond : ContinuousAt (fderiv ℝ (fderiv ℝ f)) 0 :=
    ((hf.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).continuousAt
  have hnear : ∀ᶠ x in 𝓝 (0 : E),
      ContDiffAt ℝ 2 f x ∧
        ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) 0‖ < ε := by
    exact ((hf.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).eventually
      (by norm_num)).and
      (by simpa only [dist_eq_norm] using
        Metric.tendsto_nhds.mp hsecond.tendsto ε hε)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  filter_upwards [Metric.ball_mem_nhds (0 : E) hr] with v hv
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : t • v ∈ Metric.ball (0 : E) r := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg v) ht.2).trans_lt
      (by simpa only [Metric.mem_ball, dist_zero_right] using hv)
  have hfirst (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => f (t • v)) (fderiv ℝ f (t • v) v) t := by
    have ht' : HasDerivAt (fun t : ℝ => t • v) v t := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id t).smul_const v
    exact ((hball (hseg t ht)).1.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t ht'
  have hsecond' (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => fderiv ℝ f (t • v) v)
        (fderiv ℝ (fderiv ℝ f) (t • v) v v) t := by
    have hd := ((hball (hseg t ⟨ht.1.le, ht.2.le⟩)).1.fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have ht' : HasDerivAt (fun t : ℝ => t • v) v t := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id t).smul_const v
    simpa only [Function.comp_def, map_zero, add_zero] using
      (hd.hasFDerivAt.comp_hasDerivAt t ht').clm_apply (hasDerivAt_const t v)
  have hbound (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      (a - ε) * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) (t • v) v v ∧
      fderiv ℝ (fderiv ℝ f) (t • v) v v ≤ (a + ε) * ‖v‖ ^ 2 := by
    have h := (fderiv ℝ (fderiv ℝ f) (t • v) - fderiv ℝ (fderiv ℝ f) 0).le_opNorm₂ v v
    simp only [sub_apply, Real.norm_eq_abs, hhess] at h
    have herr : |fderiv ℝ (fderiv ℝ f) (t • v) v v - a * ‖v‖ ^ 2| ≤ ε * ‖v‖ ^ 2 := by
      apply h.trans
      nlinarith [(hball (hseg t ⟨ht.1.le, ht.2.le⟩)).2,
        mul_nonneg (sub_nonneg.mpr (hball (hseg t ⟨ht.1.le, ht.2.le⟩)).2.le)
          (sq_nonneg ‖v‖)]
    obtain ⟨hl, hu⟩ := abs_le.mp herr
    constructor <;> nlinarith
  have hu := quadratic_upper_bound_of_hasDerivAt2_le (T := 1) (by norm_num)
    hfirst hsecond' (fun t ht => (hbound t ht).2)
  have hl := quadratic_upper_bound_of_hasDerivAt2_le (T := 1) (H := -(a - ε) * ‖v‖ ^ 2)
    (by norm_num) (fun t ht => (hfirst t ht).neg) (fun t ht => (hsecond' t ht).neg)
    (fun t ht => by have h := (hbound t ht).1; nlinarith)
  simp only [Pi.neg_apply, one_smul, zero_smul, hzero, zero_apply, mul_zero,
    add_zero, one_pow, mul_one, neg_zero] at hu hl
  constructor <;> linarith

end Poincare.Analysis
