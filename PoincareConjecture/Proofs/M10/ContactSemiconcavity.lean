import PoincareConjecture.Proofs.M10.ContactConcavity
import PoincareConjecture.Proofs.M10.LineSecondDerivative
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Convex.Function

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M10

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem second_deriv_affine_line_at {f : E → ℝ} (x v : E) {t : ℝ}
    (hf : ContDiffAt ℝ 2 f (x + t • v)) :
    deriv (deriv (fun s : ℝ ↦ f (x + s • v))) t =
      fderiv ℝ (fderiv ℝ f) (x + t • v) v v := by
  let F := fun s : ℝ ↦ f (x + s • v)
  have heq : (fun s : ℝ ↦ f ((x + t • v) + s • v)) = fun s ↦ F (t + s) := by
    funext s
    simp only [F, add_smul, add_assoc]
  have h := second_deriv_affine_line hf v
  rw [heq] at h
  have hfirst : deriv (fun s ↦ F (t + s)) = fun s ↦ deriv F (t + s) :=
    funext (deriv_comp_const_add F t)
  rw [hfirst, deriv_comp_const_add, add_zero] at h
  exact h

theorem second_deriv_sub_norm_sq_on_line {f : E → ℝ} (x v : E) {t : ℝ}
    (hf : ContDiffAt ℝ 2 f (x + t • v)) (K : ℝ) :
    deriv (deriv (fun s : ℝ ↦ f (x + s • v) - K * ‖x + s • v‖ ^ 2 / 2)) t =
      fderiv ℝ (fderiv ℝ f) (x + t • v) v v - K * ‖v‖ ^ 2 := by
  have hnorm (s : ℝ) : K * ‖x + s • v‖ ^ 2 / 2 =
      K * ‖x‖ ^ 2 / 2 + (K * inner ℝ x v) * s + (K * ‖v‖ ^ 2 / 2) * s ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs]
    ring
  simp_rw [hnorm]
  have hline : ContDiffAt ℝ 2 (fun s : ℝ ↦ f (x + s • v)) t :=
    hf.comp t (by fun_prop)
  rw [second_deriv_sub_quadratic hline, second_deriv_affine_line_at x v hf]
  ring

theorem concaveOn_sub_norm_sq_of_upper_contacts {s : Set E} {f : E → ℝ} {K : ℝ}
    (hs : Convex ℝ s) (hf : ContinuousOn f s)
    (hcontacts : ∀ x ∈ s, ∃ B : E → ℝ,
      B x = f x ∧ (∀ᶠ y in 𝓝 x, f y ≤ B y) ∧ ContDiffAt ℝ 2 B x ∧
        ∀ v : E, fderiv ℝ (fderiv ℝ B) x v v ≤ K * ‖v‖ ^ 2) :
    ConcaveOn ℝ s (fun x ↦ f x - K * ‖x‖ ^ 2 / 2) := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  let L := fun t : ℝ ↦ x + t • (y - x)
  have hLform (t : ℝ) : L t = (1 - t) • x + t • y := by
    dsimp only [L]
    simp only [sub_smul, one_smul, smul_sub]
    abel
  have hL : Continuous L := by dsimp only [L]; fun_prop
  have hLmem : MapsTo L (Icc 0 1) s := by
    intro t ht
    rw [hLform]
    exact hs hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
  let F := fun t ↦ f (L t) - K * ‖L t‖ ^ 2 / 2
  have hF : ContinuousOn F (Icc 0 1) :=
    (hf.comp hL.continuousOn hLmem).sub
      (show Continuous (fun t ↦ K * ‖L t‖ ^ 2 / 2) by fun_prop).continuousOn
  have hupper (c : ℝ) (hc : c ∈ Ioo 0 1) : ∃ B : ℝ → ℝ,
      B c = F c ∧ (∀ᶠ t in 𝓝 c, F t ≤ B t) ∧
        ContDiffAt ℝ 2 B c ∧ deriv (deriv B) c ≤ 0 := by
    obtain ⟨B, hBc, hupper, hB, hsecond⟩ := hcontacts (L c) (hLmem ⟨hc.1.le, hc.2.le⟩)
    refine ⟨fun t ↦ B (L t) - K * ‖L t‖ ^ 2 / 2, ?_, ?_, ?_, ?_⟩
    · simp only [hBc, F]
    · have hnear : ∀ᶠ t in 𝓝 c, f (L t) ≤ B (L t) := hL.continuousAt hupper
      exact hnear.mono (fun t ht ↦ sub_le_sub_right ht _)
    · exact (hB.comp c (by dsimp only [L]; fun_prop)).sub
        ((contDiffAt_const.mul ((show ContDiffAt ℝ 2 L c by
          dsimp only [L]; fun_prop).norm_sq ℝ)).div_const 2)
    · rw [second_deriv_sub_norm_sq_on_line x (y - x) hB K]
      exact sub_nonpos.mpr (hsecond (y - x))
  have hb1 : b ≤ 1 := by linarith
  have h := chord_le_of_upper_contacts hF hupper (x := b) ⟨hb, hb1⟩
  have h0 : L 0 = x := by simp [L]
  have h1 : L 1 = y := by simp [L]
  have hbform : L b = a • x + b • y := by
    rw [hLform, show 1 - b = a by linarith]
  simpa only [F, h0, h1, hbform, show 1 - b = a by linarith, smul_eq_mul] using h

end PoincareConjecture.M10
