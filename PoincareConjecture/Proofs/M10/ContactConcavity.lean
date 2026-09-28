import PoincareConjecture.Proofs.M10.ScalarUpperContacts
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M10

theorem second_deriv_sub_quadratic {B : ℝ → ℝ} {c : ℝ}
    (hB : ContDiffAt ℝ 2 B c) (u v ε : ℝ) :
    deriv (deriv (fun t ↦ B t - (u + v * t + ε * t ^ 2))) c =
      deriv (deriv B) c - 2 * ε := by
  let P := fun t : ℝ ↦ u + v * t + ε * t ^ 2
  have hP (t : ℝ) : HasDerivAt P (v + 2 * ε * t) t := by
    dsimp only [P]
    have hd := ((hasDerivAt_const t u).add ((hasDerivAt_id t).const_mul v)).add
      ((hasDerivAt_pow 2 t).const_mul ε)
    apply hd.congr_deriv
    simp only [mul_one, zero_add, Nat.cast_ofNat]
    ring
  have hdP : deriv P = fun t ↦ v + 2 * ε * t := funext (fun t ↦ (hP t).deriv)
  have hddP : deriv (deriv P) c = 2 * ε := by
    rw [hdP]
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id c).const_mul (2 * ε)).const_add v).deriv
  have h := iteratedDeriv_sub hB (show ContDiffAt ℝ 2 P c by dsimp [P]; fun_prop)
  have h' : deriv (deriv (B - P)) c = deriv (deriv B) c - 2 * ε := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, hddP] using h
  exact h'

theorem chord_le_of_upper_contacts {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1))
    (hcontacts : ∀ c ∈ Ioo 0 1, ∃ B : ℝ → ℝ,
      B c = f c ∧ (∀ᶠ t in 𝓝 c, f t ≤ B t) ∧
        ContDiffAt ℝ 2 B c ∧ deriv (deriv B) c ≤ 0)
    {x : ℝ} (hx : x ∈ Icc 0 1) :
    (1 - x) * f 0 + x * f 1 ≤ f x := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let P := fun t : ℝ ↦ f 0 + (f 1 - f 0 - ε) * t + ε * t ^ 2
  let h := fun t ↦ f t - P t
  have hcont : ContinuousOn h (Icc 0 1) :=
    hf.sub (show Continuous P by dsimp [P]; fun_prop).continuousOn
  have hstrict (c : ℝ) (hc : c ∈ Ioo 0 1) :
      ∃ B : ℝ → ℝ, B c = h c ∧ (∀ᶠ t in 𝓝 c, h t ≤ B t) ∧
        ContinuousAt B c ∧ deriv (deriv B) c < 0 := by
    obtain ⟨B, hBc, hupper, hB, hsecond⟩ := hcontacts c hc
    refine ⟨fun t ↦ B t - P t, ?_, ?_, ?_, ?_⟩
    · simp only [hBc, h]
    · exact hupper.mono (fun t ht ↦ sub_le_sub_right ht (P t))
    · exact hB.continuousAt.sub (by dsimp [P]; fun_prop)
    · rw [second_deriv_sub_quadratic hB]
      linarith only [hsecond, hε]
  have hbound := min_endpoints_le_of_strict_upper_contacts (by norm_num : (0 : ℝ) < 1)
    hcont hstrict hx
  have h0 : h 0 = 0 := by dsimp [h, P]; ring
  have h1 : h 1 = 0 := by dsimp [h, P]; ring
  rw [h0, h1, min_self] at hbound
  have hquadratic : x * (1 - x) ≤ 1 := by nlinarith [sq_nonneg x]
  have hεbound := mul_le_mul_of_nonneg_left hquadratic hε.le
  dsimp only [h, P] at hbound
  nlinarith only [hbound, hεbound]

end PoincareConjecture.M10
