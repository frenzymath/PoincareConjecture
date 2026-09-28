import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.NonlinearJets
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.LpNormBounds
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.DirichletForm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped ContDiff SchwartzMap LineDeriv

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "Z" => EuclideanSpace ℝ (Fin m)

def nonlinearTestSchwartz (T : V × Z → ℝ) (hT : ContDiff ℝ ∞ T)
    (hT0 : ∀ x, T (x, 0) = 0) (X : 𝓢(V, Z)) (hc : HasCompactSupport X) : 𝓢(V, ℝ) :=
  (show HasCompactSupport (fun x => T (x, X x)) from hc.mono' (by
    intro x hx
    by_contra hn
    exact hx (by
      change T (x, X x) = 0
      rw [image_eq_zero_of_notMem_tsupport hn, hT0]))).toSchwartzMap
      (hT.comp (contDiff_id.prodMk X.smooth'))

@[simp] theorem nonlinearTestSchwartz_apply (T : V × Z → ℝ) (hT : ContDiff ℝ ∞ T)
    (hT0 : ∀ x, T (x, 0) = 0) (X : 𝓢(V, Z)) (hc : HasCompactSupport X) (x : V) :
    nonlinearTestSchwartz T hT hT0 X hc x = T (x, X x) := rfl

@[simp] theorem nonlinearTestSchwartz_coe (T : V × Z → ℝ) (hT : ContDiff ℝ ∞ T)
    (hT0 : ∀ x, T (x, 0) = 0) (X : 𝓢(V, Z)) (hc : HasCompactSupport X) :
    (nonlinearTestSchwartz T hT hT0 X hc : V → ℝ) = fun x => T (x, X x) := rfl

theorem nonlinearTestSchwartz_value_norm_le
    (T : V × Z → ℝ) (hT : ContDiff ℝ ∞ T) (hT0 : ∀ x, T (x, 0) = 0)
    (X Y : 𝓢(V, Z)) (hX : HasCompactSupport X) (hY : HasCompactSupport Y)
    {C : ℝ} (hLip : ∀ x z w, ‖T (x, z) - T (x, w)‖ ≤ C * ‖z - w‖) :
    ‖(nonlinearTestSchwartz T hT hT0 X hX -
      nonlinearTestSchwartz T hT hT0 Y hY).toLp 2 volume‖ ≤ C * ‖(X - Y).toLp 2 volume‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(nonlinearTestSchwartz T hT hT0 X hX -
      nonlinearTestSchwartz T hT hT0 Y hY).coeFn_toLp 2 volume,
    (X - Y).coeFn_toLp 2 volume] with x hf hg
  rw [hf, hg]
  exact hLip x (X x) (Y x)

private theorem schwartz_partial_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (X Y : 𝓢(V, F)) (v x : V) :
    (∂_{v} (X - Y)) x = fderiv ℝ X x v - fderiv ℝ Y x v := by
  change ((LineDeriv.lineDerivOpCLM ℝ 𝓢(V, F) v) (X - Y)) x = _
  rw [map_sub, sub_apply]
  rfl

theorem nonlinearTestSchwartz_partial_norm_le
    (T : V × Z → ℝ) (hT : ContDiff ℝ ∞ T) (hT0 : ∀ x, T (x, 0) = 0)
    (X Y W : 𝓢(V, Z)) (hX : HasCompactSupport X) (hY : HasCompactSupport Y) (v : V)
    {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hspace : ∀ x z w, ‖nonlinearSpaceJet T x z v - nonlinearSpaceJet T x w v‖ ≤
      C * ‖z - w‖)
    (hval : ∀ x z, ‖nonlinearValueJet T x z‖ ≤ C)
    (hvalLip : ∀ x z w, ‖nonlinearValueJet T x z - nonlinearValueJet T x w‖ ≤ C * ‖z - w‖)
    (hW : ∀ x, ‖fderiv ℝ W x v‖ ≤ B) :
    ‖(∂_{v} (nonlinearTestSchwartz T hT hT0 X hX -
      nonlinearTestSchwartz T hT hT0 Y hY)).toLp 2 volume‖ ≤
      (C * (1 + B)) * ‖(X - Y).toLp 2 volume‖ +
        C * ‖(∂_{v} (X - Y)).toLp 2 volume‖ +
          (2 * C) * ‖(∂_{v} (Y - W)).toLp 2 volume‖ := by
  let f : Lp ℝ 2 (volume : Measure V) :=
    (∂_{v} (nonlinearTestSchwartz T hT hT0 X hX -
      nonlinearTestSchwartz T hT hT0 Y hY)).toLp 2 volume
  let g : Fin 3 → Lp Z 2 (volume : Measure V) :=
    ![(X - Y).toLp 2 volume, (∂_{v} (X - Y)).toLp 2 volume,
      (∂_{v} (Y - W)).toLp 2 volume]
  let a : Fin 3 → ℝ := ![C * (1 + B), C, 2 * C]
  have ha (i : Fin 3) : 0 ≤ a i := by
    fin_cases i
    · change 0 ≤ C * (1 + B)
      positivity
    · exact hC
    · change 0 ≤ 2 * C
      positivity
  have hb : ∀ᵐ x ∂volume, ‖f x‖ ≤ ∑ i, a i * ‖g i x‖ := by
    filter_upwards [(∂_{v} (nonlinearTestSchwartz T hT hT0 X hX -
        nonlinearTestSchwartz T hT hT0 Y hY)).coeFn_toLp 2 volume,
      (X - Y).coeFn_toLp 2 volume, (∂_{v} (X - Y)).coeFn_toLp 2 volume,
      (∂_{v} (Y - W)).coeFn_toLp 2 volume] with x hf hg0 hg1 hg2
    change ‖(∂_{v} (nonlinearTestSchwartz T hT hT0 X hX -
      nonlinearTestSchwartz T hT hT0 Y hY)).toLp 2 volume x‖ ≤ _
    rw [hf]
    simp only [schwartz_partial_sub] at hg1 hg2 ⊢
    have h := nonlinear_field_fderiv_sub_le
      (hT.differentiable (by simp) (x, X x)) (hT.differentiable (by simp) (x, Y x))
      (X.smooth'.differentiable (by simp) x) (Y.smooth'.differentiable (by simp) x)
      v (fderiv ℝ W x v) (hspace x (X x) (Y x)) (hval x (X x)) (hval x (Y x))
      (hvalLip x (X x) (Y x))
    have hlast : C * ‖X x - Y x‖ * ‖fderiv ℝ W x v‖ ≤ C * ‖X x - Y x‖ * B :=
      mul_le_mul_of_nonneg_left (hW x) (mul_nonneg hC (norm_nonneg _))
    have hout : ‖fderiv ℝ (fun y => T (y, X y)) x v -
        fderiv ℝ (fun y => T (y, Y y)) x v‖ ≤
        (C * (1 + B)) * ‖X x - Y x‖ +
          C * ‖fderiv ℝ X x v - fderiv ℝ Y x v‖ +
            (2 * C) * ‖fderiv ℝ Y x v - fderiv ℝ W x v‖ := by
      linarith only [h, hlast]
    simpa only [nonlinearTestSchwartz_coe, g, a, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero, hg0, hg1, hg2, sub_apply, add_assoc] using hout
  have h := lp_norm_le_sum f g a ha hb
  simpa only [f, g, a, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero, add_assoc] using h

end PoincareConjecture.M35.Uniqueness.Heat
