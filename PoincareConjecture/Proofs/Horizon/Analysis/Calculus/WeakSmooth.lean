import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Asymptotics
open scoped Topology ContDiff InnerProductSpace

namespace Poincare.Analysis

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

omit [FiniteDimensional ℝ E] in
private theorem exists_directional_derivative {f : E → H} {x : E}
    (hf : ∀ v : H, DifferentiableAt ℝ (fun y => inner ℝ (f y) v) x)
    (w : E) :
    ∃ z : H, ∀ v : H,
      inner ℝ z v = fderiv ℝ (fun y => inner ℝ (f y) v) x w := by
  let q : ℝ → H →L[ℝ] ℝ := fun t =>
    t⁻¹ • (InnerProductSpace.toDual ℝ H) (f (x + t • w) - f x)
  have hq : Tendsto (fun t v => q t v) (𝓝[≠] (0 : ℝ))
      (𝓝 (fun v => fderiv ℝ (fun y => inner ℝ (f y) v) x w)) := by
    apply tendsto_pi_nhds.mpr
    intro v
    have hline : HasDerivAt (fun t : ℝ => x + t • w) w 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const w |>.const_add x
    have hscalar : HasFDerivAt (fun y => inner ℝ (f y) v)
        (fderiv ℝ (fun y => inner ℝ (f y) v) x) (x + (0 : ℝ) • w) := by
      simpa using (hf v).hasFDerivAt
    have hd := hscalar.comp_hasDerivAt 0 hline
    simpa [q, Function.comp_def, inner_sub_left] using hd.tendsto_slope_zero
  let L : H →L[ℝ] ℝ := continuousLinearMapOfTendsto q hq
  refine ⟨(InnerProductSpace.toDual ℝ H).symm L, ?_⟩
  intro v
  exact InnerProductSpace.toDual_symm_apply

private theorem exists_weak_fderiv {f : E → H} {x : E}
    (hf : ∀ v : H, DifferentiableAt ℝ (fun y => inner ℝ (f y) v) x) :
    ∃ A : E →L[ℝ] H, ∀ w : E, ∀ v : H,
      inner ℝ (A w) v = fderiv ℝ (fun y => inner ℝ (f y) v) x w := by
  choose D hD using exists_directional_derivative hf
  let L : E →ₗ[ℝ] H :=
    { toFun := D
      map_add' := by
        intro w z
        apply ext_inner_right ℝ
        intro v
        simp [hD, inner_add_left]
      map_smul' := by
        intro c w
        apply ext_inner_right ℝ
        intro v
        simp [hD, inner_smul_left] }
  exact ⟨L.toContinuousLinearMap, hD⟩

private theorem scalar_quadratic_remainder {U : Set E} (hU : IsOpen U)
    {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U) {x : E} {r : ℝ}
    (hr : 0 < r) (hball : Metric.closedBall x r ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Metric.closedBall x r,
      ‖g y - g x - fderiv ℝ g x (y - x)‖ ≤ C * ‖y - x‖ ^ 2 := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ g) U :=
    hg.fderiv_of_isOpen hU (by simp)
  obtain ⟨C, hC⟩ := (hd.mono hball).exists_lipschitzOnWith
    (by simp) (convex_closedBall x r) (isCompact_closedBall x r)
  refine ⟨C, C.coe_nonneg, ?_⟩
  intro y hy
  have hx : x ∈ Metric.closedBall x r := Metric.mem_closedBall_self hr.le
  have hxy : ‖y - x‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hy
  let s := Metric.closedBall x ‖y - x‖
  have hs : s ⊆ Metric.closedBall x r := Metric.closedBall_subset_closedBall hxy
  have hsub : ∀ z ∈ s, HasFDerivWithinAt
      (fun z => g z - g x - fderiv ℝ g x (z - x))
      (fderiv ℝ g z - fderiv ℝ g x) s z := by
    intro z hz
    have hzU := hball (hs hz)
    have hzD := ((hg z hzU).contDiffAt (hU.mem_nhds hzU)).differentiableAt
      (by simp) |>.hasFDerivAt
    convert! (hzD.sub_const (g x)).sub
      ((fderiv ℝ g x).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x)) |>.hasFDerivWithinAt
      using 1
  have hbound : ∀ z ∈ s, ‖fderiv ℝ g z - fderiv ℝ g x‖ ≤ C * ‖y - x‖ := by
    intro z hz
    have hzle : ‖z - x‖ ≤ ‖y - x‖ := by
      simpa [s, Metric.mem_closedBall, dist_eq_norm] using hz
    exact (hC.norm_sub_le (hs hz) hx).trans (mul_le_mul_of_nonneg_left hzle C.coe_nonneg)
  have h := (convex_closedBall x ‖y - x‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (x := x) (y := y) hsub hbound (Metric.mem_closedBall_self (norm_nonneg _))
    (by simp [s, Metric.mem_closedBall, dist_eq_norm])
  simpa [pow_two, mul_assoc] using h

private theorem hilbert_quadratic_remainder {U : Set E} (hU : IsOpen U)
    {f : E → H} (hf : ∀ v : H, ContDiffOn ℝ ∞ (fun y => inner ℝ (f y) v) U)
    {x : E} {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall x r ⊆ U)
    (A : E →L[ℝ] H)
    (hA : ∀ w : E, ∀ v : H,
      inner ℝ (A w) v = fderiv ℝ (fun y => inner ℝ (f y) v) x w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Metric.closedBall x r,
      ‖f y - f x - A (y - x)‖ ≤ C * ‖y - x‖ ^ 2 := by
  let q : Metric.closedBall x r → H →L[ℝ] ℝ := fun y =>
    (‖(y : E) - x‖ ^ 2)⁻¹ •
      (InnerProductSpace.toDual ℝ H) (f y - f x - A ((y : E) - x))
  have hpoint : ∀ v : H, ∃ C : ℝ, ∀ y, ‖q y v‖ ≤ C := by
    intro v
    obtain ⟨C, hC0, hC⟩ := scalar_quadratic_remainder hU (hf v) hr hball
    refine ⟨C, ?_⟩
    intro y
    by_cases hy : (y : E) = x
    · simpa [q, hy] using hC0
    have hs : 0 < ‖(y : E) - x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hy))
    have hratio := (div_le_iff₀ hs).mpr (hC y y.property)
    simpa [q, inner_sub_left, hA, norm_smul, div_eq_mul_inv, mul_comm] using hratio
  obtain ⟨C, hC⟩ := banach_steinhaus hpoint
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro y hy
  by_cases hxy : y = x
  · simp [hxy]
  have hs : 0 < ‖y - x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))
  have hratio : ‖f y - f x - A (y - x)‖ / ‖y - x‖ ^ 2 ≤ C := by
    simpa only [q, norm_smul, norm_inv, norm_pow, norm_norm,
      (InnerProductSpace.toDual ℝ H).norm_map, div_eq_mul_inv, mul_comm] using hC ⟨y, hy⟩
  exact ((div_le_iff₀ hs).mp hratio).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hs.le)

private theorem differentiableAt_of_inner_smooth {U : Set E} (hU : IsOpen U)
    {f : E → H} (hf : ∀ v : H, ContDiffOn ℝ ∞ (fun y => inner ℝ (f y) v) U)
    {x : E} (hx : x ∈ U) : DifferentiableAt ℝ f x := by
  obtain ⟨A, hA⟩ := exists_weak_fderiv (fun v =>
    ((hf v x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  obtain ⟨C, hC0, hC⟩ := hilbert_quadratic_remainder hU hf hr hball A hA
  refine ⟨A, hasFDerivAt_iff_isLittleO.mpr (isLittleO_iff.mpr ?_)⟩
  intro ε hε
  have hδ : 0 < min r (ε / (C + 1)) := lt_min hr (div_pos hε (by linarith))
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  have hy' : ‖y - x‖ < min r (ε / (C + 1)) := by
    simpa [Metric.mem_ball, dist_eq_norm] using hy
  have hyball : y ∈ Metric.closedBall x r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using (lt_of_lt_of_le hy' (min_le_left _ _)).le
  have hsmall : ‖y - x‖ * (C + 1) < ε :=
    (lt_div_iff₀ (by linarith : 0 < C + 1)).mp (lt_of_lt_of_le hy' (min_le_right _ _))
  have hCsmall : C * ‖y - x‖ ≤ ε := by nlinarith [norm_nonneg (y - x)]
  exact (hC y hyball).trans (by nlinarith [norm_nonneg (y - x)])



theorem contDiffOn_of_inner_smooth
    {U : Set E} {f : E → H} (hU : IsOpen U)
    (hf : ∀ v : H, ContDiffOn ℝ ∞ (fun x => inner ℝ (f x) v) U) :
    ContDiffOn ℝ ∞ f U := by
  have hall : ∀ n : ℕ, ∀ F : E → H,
      (∀ v : H, ContDiffOn ℝ ∞ (fun x => inner ℝ (F x) v) U) →
      ContDiffOn ℝ n F U := by
    intro n
    induction n with
    | zero =>
      intro F hF
      apply contDiffOn_zero.mpr
      exact fun x hx => (differentiableAt_of_inner_smooth hU hF hx).continuousAt.continuousWithinAt
    | succ n ih =>
      intro F hF
      have hFd : DifferentiableOn ℝ F U := fun x hx =>
        (differentiableAt_of_inner_smooth hU hF hx).differentiableWithinAt
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨hFd, by simp, contDiffOn_clm_apply.mpr ?_⟩
      intro w
      apply ih
      intro v
      have hscalar := (hF v).fderiv_of_isOpen hU (by simp : ∞ + 1 ≤ ∞)
      apply (hscalar.clm_apply (contDiffOn_const (c := w))).congr
      intro x hx
      have hd := (differentiableAt_of_inner_smooth hU hF hx).hasFDerivAt.inner ℝ
        (hasFDerivAt_const v x)
      rw [hd.fderiv]
      simp
  exact contDiffOn_infty.mpr (fun n => hall n f hf)

end Poincare.Analysis
