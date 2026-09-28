import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.TwoForm
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith









set_option autoImplicit false

open scoped BigOperators

namespace Poincare.RicciFlow.Harnack

variable {I : Type*} [Fintype I] [DecidableEq I]



lemma derivative_contraction_prescribed_jet
    (dP : I → I → I → I → ℝ) (Ric B : I → I → ℝ) (W : I → ℝ) (k : ℝ)
    (hskew : ∀ e a b c, dP e a b c = -dP e b a c)
    (hdiv : ∀ b c, (∑ e, dP e e b c) = B b c) :
    (∑ e, ∑ a, ∑ b, ∑ c, dP e a b c *
      (((Ric e a + k * (if e = a then 1 else 0)) * W b -
        W a * (Ric e b + k * (if e = b then 1 else 0))) / 2) * W c) =
      (∑ e, ∑ a, ∑ b, ∑ c, dP e a b c * Ric e a * W b * W c) +
        k * (∑ b, ∑ c, B b c * W b * W c) := by
  have hjet (e : I) :
      (∑ a, ∑ b, ∑ c, dP e a b c *
        (((Ric e a + k * (if e = a then 1 else 0)) * W b -
          W a * (Ric e b + k * (if e = b then 1 else 0))) / 2) * W c) =
        ∑ a, ∑ b, ∑ c, dP e a b c *
          (Ric e a + k * (if e = a then 1 else 0)) * W b * W c := by
    rw [Finset.sum_comm_cycle]
    conv_rhs => rw [Finset.sum_comm_cycle]
    apply Finset.sum_congr rfl
    intro c _
    simpa only [Finset.sum_mul] using congrArg (fun q : ℝ => q * W c)
      (skew_contraction_half_wedge (fun a b => dP e a b c)
        (fun a b => hskew e a b c)
        (fun a => Ric e a + k * (if e = a then 1 else 0)) W)
  simp_rw [hjet]
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  congr 1
  have hdelta (e a b c : I) :
      dP e a b c * (k * (if e = a then 1 else 0)) * W b * W c =
        if a = e then k * (dP e e b c * W b * W c) else 0 := by
    by_cases h : a = e
    · subst a
      simp only [if_true, mul_one]
      ring
    · simp [h, Ne.symm h]
  simp_rw [hdelta]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.sum_mul, ← Finset.sum_mul, hdiv]



lemma curvature_derivative_contraction_prescribed_jet
    (dR : I → I → I → I → I → ℝ) (Ric : I → I → ℝ)
    (P : I → I → I → ℝ) (U : I → I → ℝ) (W : I → ℝ) (k : ℝ)
    (hskew : ∀ e a b c d, dR e a b c d = -dR e b a c d)
    (hdiv : ∀ b c d, (∑ e, dR e e b c d) = P c d b) :
    (∑ e, ∑ a, ∑ b, ∑ c, ∑ d, dR e a b c d *
      (((Ric e a + k * (if e = a then 1 else 0)) * W b -
        W a * (Ric e b + k * (if e = b then 1 else 0))) / 2) * U c d) =
      (∑ e, ∑ a, ∑ b, ∑ c, ∑ d, dR e a b c d * Ric e a * W b * U c d) +
        k * (∑ b, ∑ c, ∑ d, P c d b * W b * U c d) := by
  have hjet (e : I) :
      (∑ a, ∑ b, ∑ c, ∑ d, dR e a b c d *
        (((Ric e a + k * (if e = a then 1 else 0)) * W b -
          W a * (Ric e b + k * (if e = b then 1 else 0))) / 2) * U c d) =
        ∑ a, ∑ b, ∑ c, ∑ d, dR e a b c d *
          (Ric e a + k * (if e = a then 1 else 0)) * W b * U c d := by
    rw [Finset.sum_comm_cycle]
    conv_rhs => rw [Finset.sum_comm_cycle]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_comm_cycle]
    conv_rhs => rw [Finset.sum_comm_cycle]
    apply Finset.sum_congr rfl
    intro d _
    simpa only [Finset.sum_mul] using congrArg (fun q : ℝ => q * U c d)
      (skew_contraction_half_wedge (fun a b => dR e a b c d)
        (fun a b => hskew e a b c d)
        (fun a => Ric e a + k * (if e = a then 1 else 0)) W)
  simp_rw [hjet]
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  congr 1
  have hdelta (e a b c d : I) :
      dR e a b c d * (k * (if e = a then 1 else 0)) * W b * U c d =
        if a = e then k * (dR e e b c d * W b * U c d) else 0 := by
    by_cases h : a = e
    · subst a
      simp only [if_true, mul_one]
      ring
    · simp [h, Ne.symm h]
  simp_rw [hdelta]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_mul, ← Finset.sum_mul, hdiv]

omit [DecidableEq I] in


lemma curvature_derivative_ricci_cancellation
    (dR : I → I → I → I → I → ℝ) (Ric U : I → I → ℝ) (W : I → ℝ)
    (hpair : ∀ e a b c d, dR e a b c d = dR e c d a b)
    (hlast : ∀ e a b c d, dR e a b c d = -dR e a b d c) :
    (∑ e, ∑ a, ∑ b, ∑ c, ∑ d, dR e a b c d * Ric e a * W b * U c d) +
      (∑ a, ∑ b, ∑ c, ∑ e, ∑ d, Ric e d * dR e a b c d * U a b * W c) = 0 := by
  let σ : (I × I × I × I × I) ≃ (I × I × I × I × I) :=
    { toFun := fun (e, a, b, c, d) => (c, d, b, e, a)
      invFun := fun (a, b, c, e, d) => (e, d, c, a, b)
      left_inv := by rintro ⟨e, a, b, c, d⟩; rfl
      right_inv := by rintro ⟨a, b, c, e, d⟩; rfl }
  have he := Fintype.sum_equiv σ
    (fun (e, a, b, c, d) => dR e a b c d * Ric e a * W b * U c d)
    (fun (a, b, c, e, d) => -(Ric e d * dR e a b c d * U a b * W c))
    (by
      rintro ⟨e, a, b, c, d⟩
      dsimp [σ]
      rw [hpair e a b c d, hlast e c d a b]
      ring)
  simp only [Fintype.sum_prod_type, Finset.sum_neg_distrib] at he
  linarith only [he]



lemma curvature_contraction_prescribed_jets
    (R : I → I → I → I → ℝ) (Ric : I → I → ℝ) (W : I → ℝ) (k : ℝ)
    (hfirst : ∀ a b c d, R a b c d = -R b a c d)
    (hlast : ∀ a b c d, R a b c d = -R a b d c)
    (hRic : ∀ b d, (∑ e, R e b e d) = Ric b d)
    (hsymm : ∀ a b, Ric a b = Ric b a) :
    (∑ e, ∑ a, ∑ b, ∑ c, ∑ d, R a b c d *
      (((Ric e a + k * (if e = a then 1 else 0)) * W b -
        W a * (Ric e b + k * (if e = b then 1 else 0))) / 2) *
      (((Ric e c + k * (if e = c then 1 else 0)) * W d -
        W c * (Ric e d + k * (if e = d then 1 else 0))) / 2)) =
      (∑ e, ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * Ric e a * W b * Ric e c * W d) +
      2 * k * (∑ a, ∑ b, ∑ c, ∑ d, R a b c d * Ric a c * W b * W d) +
      k ^ 2 * (∑ b, ∑ d, Ric b d * W b * W d) := by
  simp_rw [curvature_contraction_half_wedge R hfirst hlast]
  have hterm (e a b c d : I) :
      R a b c d * (Ric e a + k * (if e = a then 1 else 0)) * W b *
        (Ric e c + k * (if e = c then 1 else 0)) * W d =
      R a b c d * Ric e a * W b * Ric e c * W d +
        k * (if c = e then R a b e d * Ric e a * W b * W d else 0) +
        k * (if a = e then R e b c d * Ric e c * W b * W d else 0) +
        k ^ 2 * (if a = e then if c = e then R e b e d * W b * W d else 0 else 0) := by
    by_cases ha : a = e <;> by_cases hc : c = e <;>
      simp [ha, hc, Ne.symm, eq_comm] <;> ring
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hcross : (∑ e, ∑ a, ∑ b, ∑ d, R a b e d * Ric e a * W b * W d) =
      ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * Ric a c * W b * W d := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    simp_rw [hsymm _ a]
  have htrace : (∑ e, ∑ b, ∑ d, R e b e d * W b * W d) =
      ∑ b, ∑ d, Ric b d * W b * W d := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    rw [← Finset.sum_mul, ← Finset.sum_mul, hRic]
  rw [hcross, htrace]
  ring



lemma hamiltonM_prescribed_jet_cancellation
    (R : I → I → I → I → ℝ) (dP : I → I → I → I → ℝ)
    (Ric M : I → I → ℝ) (W : I → ℝ) (k : ℝ)
    (hfirst : ∀ a b c d, R a b c d = -R b a c d)
    (hlast : ∀ a b c d, R a b c d = -R a b d c)
    (hRic : ∀ b d, (∑ e, R e b e d) = Ric b d)
    (hsymm : ∀ a b, Ric a b = Ric b a)
    (hskew : ∀ e a b c, dP e a b c = -dP e b a c)
    (hdiv : ∀ b d, (∑ e, dP e e b d) =
      M b d - (∑ a, ∑ c, R a b c d * Ric a c) - k * Ric b d) :
    let V := fun e a b =>
      ((Ric e a + k * (if e = a then 1 else 0)) * W b -
        W a * (Ric e b + k * (if e = b then 1 else 0))) / 2
    2 * (∑ e, ∑ a, ∑ b, ∑ c, Ric e a * (dP e a b c + dP e a c b) * W b * W c) -
      4 * (∑ e, ∑ a, ∑ b, ∑ c, dP e a b c * V e a b * W c) +
      4 * k * (∑ b, ∑ d, M b d * W b * W d) -
      2 * k ^ 2 * (∑ b, ∑ d, Ric b d * W b * W d) +
      2 * (∑ e, ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * Ric e a * W b * Ric e c * W d) -
      2 * (∑ e, ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * V e a b * V e c d) = 0 := by
  dsimp only
  have hd := derivative_contraction_prescribed_jet dP Ric
    (fun b d => M b d - (∑ a, ∑ c, R a b c d * Ric a c) - k * Ric b d)
    W k hskew hdiv
  have hq := curvature_contraction_prescribed_jets R Ric W k hfirst hlast hRic hsymm
  have hgrad :
      (∑ e, ∑ a, ∑ b, ∑ c, Ric e a * (dP e a b c + dP e a c b) * W b * W c) =
        2 * (∑ e, ∑ a, ∑ b, ∑ c, dP e a b c * Ric e a * W b * W c) := by
    have hswap (e a : I) :
        (∑ b, ∑ c, Ric e a * dP e a c b * W b * W c) =
          ∑ b, ∑ c, Ric e a * dP e a b c * W b * W c := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      ring
    simp only [mul_add, add_mul, Finset.sum_add_distrib, hswap]
    simp only [mul_comm (Ric _ _) (dP _ _ _ _)]
    ring
  have hcurv :
      (∑ b, ∑ d, (∑ a, ∑ c, R a b c d * Ric a c) * W b * W d) =
        ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * Ric a c * W b * W d := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm_cycle]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_comm]
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc k, ← Finset.mul_sum] at hd
  rw [hcurv] at hd
  rw [hgrad, hd, hq]
  ring



lemma hamiltonP_prescribed_jet_cancellation
    (dR : I → I → I → I → I → ℝ) (Ric : I → I → ℝ)
    (P : I → I → I → ℝ) (U : I → I → ℝ) (W : I → ℝ) (k : ℝ)
    (hfirst : ∀ e a b c d, dR e a b c d = -dR e b a c d)
    (hpair : ∀ e a b c d, dR e a b c d = dR e c d a b)
    (hlast : ∀ e a b c d, dR e a b c d = -dR e a b d c)
    (hdiv : ∀ b c d, (∑ e, dR e e b c d) = P c d b) :
    let V := fun e a b =>
      ((Ric e a + k * (if e = a then 1 else 0)) * W b -
        W a * (Ric e b + k * (if e = b then 1 else 0))) / 2;
    -(4 * (∑ a, ∑ b, ∑ c, ∑ e, ∑ d, Ric e d * dR e a b c d * U a b * W c)) +
      4 * k * (∑ a, ∑ b, ∑ c, P a b c * U a b * W c) -
      4 * (∑ e, ∑ a, ∑ b, ∑ c, ∑ d, dR e a b c d * V e a b * U c d) = 0 := by
  dsimp only
  rw [curvature_derivative_contraction_prescribed_jet dR Ric P U W k hfirst hdiv]
  have hc := curvature_derivative_ricci_cancellation dR Ric U W hpair hlast
  have horder : (∑ b, ∑ c, ∑ d, P c d b * W b * U c d) =
      ∑ a, ∑ b, ∑ c, P a b c * U a b * W c := by
    rw [Finset.sum_comm_cycle, Finset.sum_comm_cycle]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [horder]
  linarith only [hc]

end Poincare.RicciFlow.Harnack
