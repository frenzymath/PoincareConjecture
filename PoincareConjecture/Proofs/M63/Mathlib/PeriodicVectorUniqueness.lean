import PoincareConjecture.Proofs.M63.Mathlib.PeriodicMaximumPrinciple
import Mathlib.Analysis.InnerProductSpace.Calculus









set_option autoImplicit false

open Set
open scoped RealInnerProductSpace

namespace PoincareConjecture.M63





theorem periodic_vector_eq_zero_of_parabolic_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {w wx wxx wt : ℝ → ℝ → E} {A : ℝ → ℝ → ℝ} {p a b alpha C : ℝ}
    (hp : 0 < p) (hab : a < b) (halpha : 0 < alpha) (_hC : 0 ≤ C)
    (hw : ContinuousOn (Function.uncurry w) (univ ×ˢ Icc a b))
    (hper : ∀ t ∈ Icc a b, Function.Periodic (fun x => w x t) p)
    (hx : ∀ x t, t ∈ Ioo a b → HasDerivAt (fun y => w y t) (wx x t) x)
    (hxx : ∀ x t, t ∈ Ioo a b → HasDerivAt (fun y => wx y t) (wxx x t) x)
    (htime : ∀ x t, t ∈ Ioo a b → HasDerivAt (w x) (wt x t) t)
    (hA : ∀ x t, t ∈ Ioo a b → alpha ≤ A x t)
    (herror : ∀ x t, t ∈ Ioo a b →
      ‖wt x t - A x t • wxx x t‖ ≤ C * (‖w x t‖ + ‖wx x t‖))
    (hinit : ∀ x, w x a = 0) :
    ∀ x t, t ∈ Icc a b → w x t = 0 := by
  let K := 2 * C + C ^ 2 / alpha
  have hsecond (x t : ℝ) (ht : t ∈ Ioo a b) :
      deriv (deriv (fun y => ‖w y t‖ ^ 2)) x =
        2 * ‖wx x t‖ ^ 2 + 2 * ⟪w x t, wxx x t⟫ := by
    have hfirst : deriv (fun y => ‖w y t‖ ^ 2) =
        fun y => 2 * ⟪w y t, wx y t⟫ := funext (fun y => (hx y t ht).norm_sq.deriv)
    rw [hfirst, (((hx x t ht).inner ℝ (hxx x t ht)).const_mul 2).deriv]
    rw [real_inner_self_eq_norm_sq]
    ring
  have hpde (x t : ℝ) (ht : t ∈ Ioo a b) :
      2 * ⟪w x t, wt x t⟫ ≤
        A x t * deriv (deriv (fun y => ‖w y t‖ ^ 2)) x + K * ‖w x t‖ ^ 2 := by
    have hinner : ⟪w x t, wt x t - A x t • wxx x t⟫ ≤
        ‖w x t‖ * (C * (‖w x t‖ + ‖wx x t‖)) :=
      (real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (herror x t ht) (norm_nonneg _))
    rw [inner_sub_right, real_inner_smul_right] at hinner
    have hyoung : 2 * C * ‖w x t‖ * ‖wx x t‖ ≤
        alpha * ‖wx x t‖ ^ 2 + (C ^ 2 / alpha) * ‖w x t‖ ^ 2 := by
      apply (mul_le_mul_iff_right₀ halpha).mp
      have hcancel : (C ^ 2 / alpha) * ‖w x t‖ ^ 2 * alpha = C ^ 2 * ‖w x t‖ ^ 2 := by
        field_simp
      nlinarith only [sq_nonneg (C * ‖w x t‖ - alpha * ‖wx x t‖), hcancel]
    have helliptic := mul_le_mul_of_nonneg_right (hA x t ht) (sq_nonneg ‖wx x t‖)
    rw [hsecond x t ht]
    dsimp only [K]
    nlinarith only [hinner, hyoung, helliptic,
      mul_nonneg halpha.le (sq_nonneg ‖wx x t‖)]
  have hzero := Poincare.Parabolic.periodic_nonpos_of_parabolic_le
    (F := fun x t => ‖w x t‖ ^ 2) (V := fun x t => 2 * ⟪w x t, wt x t⟫)
    (A := A) (B := fun _ _ => 0) (C := fun _ _ => K) (K := K) hp hab
    (by convert! hw.norm.pow 2 using 1)
    (fun t ht x => congrArg (fun z : E => ‖z‖ ^ 2) (hper t ht x))
    (fun x t ht => (htime x t ht).norm_sq)
    (fun x t ht => halpha.le.trans (hA x t ht)) (fun _ _ _ => le_rfl)
    (fun x t ht => by simpa only [zero_mul, add_zero] using hpde x t ht)
    (fun x => by simp only [hinit, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), le_refl])
  intro x t ht
  apply norm_eq_zero.mp
  nlinarith only [hzero x t ht, norm_nonneg (w x t)]

end PoincareConjecture.M63
