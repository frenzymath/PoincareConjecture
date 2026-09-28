import Mathlib.Analysis.Calculus.ContDiff.Bounds









set_option autoImplicit false

open Set
open scoped ContDiff BigOperators

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]




theorem norm_iteratedFDeriv_smul_le_of_local_bounds
    {U : Set E} (hU : IsOpen U) {f : E → ℝ} {g : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {x : E} (hx : x ∈ U) (m : ℕ) {A B : ℝ} (hA : 0 ≤ A)
    (hfbound : ∀ j ≤ m, ‖iteratedFDeriv ℝ j f x‖ ≤ A)
    (hgbound : ∀ j ≤ m, ‖iteratedFDeriv ℝ j g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ m (fun y => f y • g y) x‖ ≤
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * A * B := by
  have hfi (j : ℕ) : iteratedFDerivWithin ℝ j f U x = iteratedFDeriv ℝ j f x :=
    iteratedFDerivWithin_eq_iteratedFDeriv (n := j) hU.uniqueDiffOn
      ((hf.contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast le_top)) hx
  have hgi (j : ℕ) : iteratedFDerivWithin ℝ j g U x = iteratedFDeriv ℝ j g x :=
    iteratedFDerivWithin_eq_iteratedFDeriv (n := j) hU.uniqueDiffOn
      ((hg.contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast le_top)) hx
  have hfg : iteratedFDerivWithin ℝ m (fun y => f y • g y) U x =
      iteratedFDeriv ℝ m (fun y => f y • g y) x :=
    iteratedFDerivWithin_eq_iteratedFDeriv (n := m) hU.uniqueDiffOn
      (((hf.smul hg).contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast le_top)) hx
  have hb := norm_iteratedFDerivWithin_smul_le hf hg hU.uniqueDiffOn hx
    (n := m) (by exact_mod_cast le_top)
  simp only [hfg, hfi, hgi] at hb
  apply hb.trans
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (hfbound i (by simpa using Finset.mem_range.mp hi))
      (Nat.cast_nonneg _))
    (hgbound (m - i) (Nat.sub_le _ _)) (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) hA)




theorem norm_iteratedFDeriv_blend_le_of_local_bounds
    {U : Set E} (hU : IsOpen U) {θ : E → ℝ} {f g : E → F}
    (hθ : ContDiffOn ℝ ∞ θ U) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {x : E} (hx : x ∈ U) (m : ℕ) {A B : ℝ} (hA : 0 ≤ A)
    (hθbound : ∀ j ≤ m, ‖iteratedFDeriv ℝ j θ x‖ ≤ A)
    (hcompbound : ∀ j ≤ m, ‖iteratedFDeriv ℝ j (fun y => 1 - θ y) x‖ ≤ A)
    (hfbound : ∀ j ≤ m, ‖iteratedFDeriv ℝ j f x‖ ≤ B)
    (hgbound : ∀ j ≤ m, ‖iteratedFDeriv ℝ j g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ m (fun y => (1 - θ y) • f y + θ y • g y) x‖ ≤
      2 * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * A * B := by
  have hcomp : ContDiffOn ℝ ∞ (fun y => 1 - θ y) U := contDiffOn_const.sub hθ
  have hl := norm_iteratedFDeriv_smul_le_of_local_bounds hU hcomp hf hx m hA
    hcompbound hfbound
  have hr := norm_iteratedFDeriv_smul_le_of_local_bounds hU hθ hg hx m hA hθbound hgbound
  change ‖iteratedFDeriv ℝ m (((fun y => 1 - θ y) • f) + θ • g) x‖ ≤ _
  rw [iteratedFDeriv_add_apply (i := m)
    (((hcomp.smul hf).contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast le_top))
    (((hθ.smul hg).contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast le_top))]
  apply (norm_add_le _ _).trans
  change ‖iteratedFDeriv ℝ m (fun y => (1 - θ y) • f y) x‖ +
    ‖iteratedFDeriv ℝ m (fun y => θ y • g y) x‖ ≤ _
  linarith
