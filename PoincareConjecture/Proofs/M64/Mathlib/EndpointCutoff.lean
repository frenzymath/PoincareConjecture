import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture

private def step (j : ℕ) (x : ℝ) : ℝ :=
  Real.smoothTransition (((j : ℝ) + 1) * x - 1)

private theorem step_smooth (j : ℕ) : ContDiff ℝ ∞ (step j) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

private theorem step_deriv (j : ℕ) (x : ℝ) :
    deriv (step j) x = ((j : ℝ) + 1) *
      deriv Real.smoothTransition (((j : ℝ) + 1) * x - 1) := by
  have h := ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ _).differentiable
    (by simp) _).hasDerivAt.comp x (((hasDerivAt_id x).const_mul ((j : ℝ) + 1)).sub_const 1)
  change deriv (fun y : ℝ => Real.smoothTransition (((j : ℝ) + 1) * y - 1)) x = _
  simpa only [Function.comp_def, id_eq, mul_one, one_mul, mul_comm] using h.deriv

private theorem transition_deriv_zero {x : ℝ} (hx : x ≤ 0 ∨ 1 ≤ x) :
    deriv Real.smoothTransition x = 0 := by
  rcases hx with hx | hx
  · apply IsLocalMin.deriv_eq_zero
    filter_upwards [] with y
    rw [Real.smoothTransition.zero_of_nonpos hx]
    exact Real.smoothTransition.nonneg y
  · apply IsLocalMax.deriv_eq_zero
    filter_upwards [] with y
    rw [Real.smoothTransition.one_of_one_le hx]
    exact Real.smoothTransition.le_one y

private theorem transition_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |deriv Real.smoothTransition x| ≤ C := by
  have hc := (Real.smoothTransition.contDiff : ContDiff ℝ ∞ _).continuous_deriv (by simp)
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro x
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · exact (hB x hx).trans (le_max_left _ _)
  · have hz : x ≤ 0 ∨ 1 ≤ x := by
      simp only [mem_Icc, not_and_or, not_le] at hx
      grind
    rw [transition_deriv_zero hz, abs_zero]
    exact le_max_right _ _

private theorem step_weighted_bound {C L x z : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hbound : ∀ t, |deriv Real.smoothTransition t| ≤ C)
    (hz : |z| ≤ L * |x|) (j : ℕ) :
    |deriv (step j) x * z| ≤ 2 * C * L := by
  have hk : 0 < (j : ℝ) + 1 := by positivity
  rw [step_deriv]
  by_cases hx : ((j : ℝ) + 1) * x - 1 ∈ Ioo (0 : ℝ) 1
  · have hx0 : 0 ≤ x := by nlinarith [hx.1]
    rw [abs_mul, abs_mul, abs_of_pos hk]
    calc
      _ ≤ (((j : ℝ) + 1) * C) * (L * |x|) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hbound _) hk.le) hz
          (abs_nonneg _) (mul_nonneg hk.le hC)
      _ = C * L * (((j : ℝ) + 1) * x) := by rw [abs_of_nonneg hx0]; ring
      _ ≤ 2 * C * L := by
        have hh := mul_le_mul_of_nonneg_left (show ((j : ℝ) + 1) * x ≤ 2 by
          linarith [hx.2]) (mul_nonneg hC hL)
        nlinarith
  · have hz' : ((j : ℝ) + 1) * x - 1 ≤ 0 ∨ 1 ≤ ((j : ℝ) + 1) * x - 1 := by
      simpa only [mem_Ioo, not_and_or, not_lt] using hx
    rw [transition_deriv_zero hz', mul_zero, zero_mul, abs_zero]
    positivity

private theorem step_eventually {x : ℝ} (hx : 0 < x) :
    ∀ᶠ j : ℕ in atTop, step j x = 1 ∧ deriv (step j) x = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / x)
  filter_upwards [eventually_ge_atTop N] with j hj
  have hNj : (N : ℝ) ≤ j := by exact_mod_cast hj
  have hh : 1 ≤ ((j : ℝ) + 1) * x - 1 := by
    have := (div_lt_iff₀ hx).mp hN
    nlinarith
  exact ⟨Real.smoothTransition.one_of_one_le hh, by
    rw [step_deriv, transition_deriv_zero (Or.inr hh), mul_zero]⟩

def m64EndpointCutoff (a b : ℝ) (f : ℝ → ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  f x * step j (x - a) * step j (b - x)

theorem m64EndpointCutoff_contDiff {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (j : ℕ) : ContDiff ℝ ∞ (m64EndpointCutoff a b f j) :=
  (hf.mul ((step_smooth j).comp (contDiff_id.sub contDiff_const))).mul
    ((step_smooth j).comp (contDiff_const.sub contDiff_id))

theorem m64EndpointCutoff_tsupport {a b : ℝ} {f : ℝ → ℝ} (j : ℕ) :
    tsupport (m64EndpointCutoff a b f j) ⊆
      Icc (a + 1 / ((j : ℝ) + 1)) (b - 1 / ((j : ℝ) + 1)) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hk : 0 < (j : ℝ) + 1 := by positivity
  have hl : 0 < ((j : ℝ) + 1) * (x - a) - 1 := by
    by_contra! hh
    apply hx
    simp only [m64EndpointCutoff, step, Real.smoothTransition.zero_of_nonpos hh,
      mul_zero, zero_mul]
  have hr : 0 < ((j : ℝ) + 1) * (b - x) - 1 := by
    by_contra! hh
    apply hx
    simp only [m64EndpointCutoff, step, Real.smoothTransition.zero_of_nonpos hh, mul_zero]
  constructor
  · have h := (div_le_iff₀ hk).mpr (show 1 ≤ (x - a) * ((j : ℝ) + 1) by nlinarith)
    linarith
  · have h := (div_le_iff₀ hk).mpr (show 1 ≤ (b - x) * ((j : ℝ) + 1) by nlinarith)
    linarith

theorem m64EndpointCutoff_compact {a b : ℝ} {f : ℝ → ℝ} (j : ℕ) :
    HasCompactSupport (m64EndpointCutoff a b f j) ∧
      tsupport (m64EndpointCutoff a b f j) ⊆ Ioo a b := by
  refine ⟨isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (m64EndpointCutoff_tsupport j), ?_⟩
  intro x hx
  have hh := m64EndpointCutoff_tsupport j hx
  have hk : 0 < 1 / ((j : ℝ) + 1) := by positivity
  exact ⟨by linarith [hh.1], by linarith [hh.2]⟩

private theorem cutoff_deriv {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (j : ℕ) (x : ℝ) :
    deriv (m64EndpointCutoff a b f j) x =
      deriv f x * step j (x - a) * step j (b - x) +
      (deriv (step j) (x - a) * f x) * step j (b - x) -
      (deriv (step j) (b - x) * f x) * step j (x - a) := by
  have hl := ((step_smooth j).differentiable (by simp) (x - a)).hasDerivAt.comp x
    ((hasDerivAt_id x).sub_const a)
  have hr := ((step_smooth j).differentiable (by simp) (b - x)).hasDerivAt.comp x
    ((hasDerivAt_id x).const_sub b)
  have h := (((hf.differentiable (by simp) x).hasDerivAt.mul hl).mul hr).deriv
  change deriv (m64EndpointCutoff a b f j) x = _ at h
  rw [h]
  simp only [Function.comp_apply, Pi.mul_apply, id_eq]
  ring

theorem m64EndpointCutoff_eventually {a b x : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hx : x ∈ Ioo a b) :
    ∀ᶠ j : ℕ in atTop, m64EndpointCutoff a b f j x = f x ∧
      deriv (m64EndpointCutoff a b f j) x = deriv f x := by
  filter_upwards [step_eventually (sub_pos.mpr hx.1),
    step_eventually (sub_pos.mpr hx.2)] with j hl hr
  rw [cutoff_deriv hf]
  simp only [m64EndpointCutoff, hl.1, hl.2, hr.1, hr.2, mul_one, zero_mul,
    add_zero, sub_zero, and_self]

theorem m64EndpointCutoff_uniform_bound {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (ha : f a = 0) (hb : f b = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j x, x ∈ Icc a b →
      |m64EndpointCutoff a b f j x| ≤ C ∧
        |deriv (m64EndpointCutoff a b f j) x| ≤ C := by
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
    ((hf.continuous.norm.add (hf.continuous_deriv (by simp)).norm).continuousOn)
  obtain ⟨L, hL⟩ := hf.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_Icc a b) isCompact_Icc
  obtain ⟨D, hD, hd⟩ := transition_deriv_bound
  refine ⟨max B 0 + 4 * D * L, by positivity, ?_⟩
  intro j x hx
  have hab := hx.1.trans hx.2
  have hleft : |f x| ≤ L * |x - a| := by
    simpa only [Real.dist_eq, ha, sub_zero] using hL.dist_le_mul x hx a (left_mem_Icc.mpr hab)
  have hright : |f x| ≤ L * |b - x| := by
    simpa only [Real.dist_eq, hb, zero_sub, abs_neg] using
      hL.dist_le_mul b (right_mem_Icc.mpr hab) x hx
  have hsum : |f x| + |deriv f x| ≤ B := by
    have h := hB x hx
    change ‖‖f x‖ + ‖deriv f x‖‖ ≤ B at h
    simp only [Real.norm_eq_abs] at h
    rwa [abs_of_nonneg (add_nonneg (abs_nonneg (f x)) (abs_nonneg (deriv f x)))] at h
  have hs (y : ℝ) : |step j y| ≤ 1 := by
    change |Real.smoothTransition _| ≤ 1
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hmul (z y : ℝ) : |z * step j y| ≤ |z| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hs y)
  constructor
  · exact ((hmul _ _).trans (hmul _ _)).trans (by
      linarith [le_max_left B 0, mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hD)
        L.coe_nonneg, abs_nonneg (deriv f x)])
  · rw [cutoff_deriv hf]
    have hl := (hmul (deriv (step j) (x - a) * f x) (b - x)).trans
      (step_weighted_bound hD L.coe_nonneg hd hleft j)
    have hr := (hmul (deriv (step j) (b - x) * f x) (x - a)).trans
      (step_weighted_bound hD L.coe_nonneg hd hright j)
    have hv := (hmul (deriv f x * step j (x - a)) (b - x)).trans
      (hmul (deriv f x) (x - a))
    calc
      _ ≤ |deriv f x * step j (x - a) * step j (b - x)| +
          |deriv (step j) (x - a) * f x * step j (b - x)| +
          |deriv (step j) (b - x) * f x * step j (x - a)| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ |deriv f x| + 2 * D * L + 2 * D * L := add_le_add (add_le_add hv hl) hr
      _ ≤ max B 0 + 4 * D * L := by
        nlinarith [le_max_left B 0, abs_nonneg (f x)]

end PoincareConjecture
