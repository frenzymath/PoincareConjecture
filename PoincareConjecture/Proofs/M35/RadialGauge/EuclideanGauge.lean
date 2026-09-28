import PoincareConjecture.Proofs.M35.RadialGauge.CorrectedEquation
import PoincareConjecture.Proofs.M07.Analysis.Calculus.Diffeomorphism.Perturbation
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff NNReal

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

noncomputable def euclideanGauge (u : V → ℝ) (x : V) : V := Real.exp (u x) • x

theorem euclideanGauge_hasFDerivAt {u : V → ℝ} {x : V}
    (hu : DifferentiableAt ℝ u x) :
    HasFDerivAt (euclideanGauge u)
      (Real.exp (u x) • ContinuousLinearMap.id ℝ V +
        (Real.exp (u x) • fderiv ℝ u x).smulRight x) x := by
  have hscalar : HasFDerivAt (fun y : V => Real.exp (u y))
      ((Real.exp (u x)) • fderiv ℝ u x) x := hu.hasFDerivAt.exp
  have h := hscalar.smul (hasFDerivAt_id x)
  change HasFDerivAt (fun y : V => Real.exp (u y) • y)
      (Real.exp (u x) • ContinuousLinearMap.id ℝ V +
        (Real.exp (u x) • fderiv ℝ u x).smulRight x) x at h
  change HasFDerivAt (fun y : V => Real.exp (u y) • y)
      (Real.exp (u x) • ContinuousLinearMap.id ℝ V +
        (Real.exp (u x) • fderiv ℝ u x).smulRight x) x
  exact h

theorem euclideanGauge_sub_id_fderiv_bound {u : V → ℝ} {x : V}
    (hu : DifferentiableAt ℝ u x)
    (hv : (1 + ‖x‖) * |u x| ≤ 1 / 8)
    (hd : (1 + ‖x‖) * ‖fderiv ℝ u x‖ ≤ 1 / 8) :
    ‖fderiv ℝ (fun y => euclideanGauge u y - y) x‖ ≤ 1 / 2 := by
  have hv' : |u x| ≤ 1 / 8 := by
    nlinarith [mul_nonneg (norm_nonneg x) (abs_nonneg (u x))]
  have he : |Real.exp (u x) - 1| ≤ 1 / 4 :=
    (Real.abs_exp_sub_one_le (by linarith)).trans (by linarith)
  have he2 : Real.exp (u x) ≤ 2 := by
    have h := le_abs_self (Real.exp (u x) - 1)
    linarith
  have hd' : ‖fderiv ℝ u x‖ * ‖x‖ ≤ 1 / 8 := by
    nlinarith [norm_nonneg (fderiv ℝ u x)]
  have hderiv := (euclideanGauge_hasFDerivAt hu).sub (hasFDerivAt_id x)
  change ‖fderiv ℝ (euclideanGauge u - (id : V → V)) x‖ ≤ 1 / 2
  rw [hderiv.fderiv]
  have heq : Real.exp (u x) • ContinuousLinearMap.id ℝ V +
      (Real.exp (u x) • fderiv ℝ u x).smulRight x - ContinuousLinearMap.id ℝ V =
      (Real.exp (u x) - 1) • ContinuousLinearMap.id ℝ V +
        (Real.exp (u x) • fderiv ℝ u x).smulRight x := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [add_apply, sub_apply,
      ContinuousLinearMap.smulRight_apply, smul_apply,
      ContinuousLinearMap.id_apply]
    have hv : Real.exp (u x) • v - v = (Real.exp (u x) - 1) • v := by
      simpa only [one_smul] using
        (sub_smul (Real.exp (u x)) (1 : ℝ) v).symm
    calc
      _ = (Real.exp (u x) • v - v) +
          (Real.exp (u x) • (fderiv ℝ u x) v) • x := by abel
      _ = _ := by rw [hv]
  rw [heq]
  have h1 : ‖((Real.exp (u x)) • fderiv ℝ u x).smulRight x‖ ≤ 1 / 4 := by
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs, Real.abs_exp]
    nlinarith [mul_nonneg (Real.exp_nonneg (u x))
      (sub_nonneg.mpr hd'), mul_nonneg (sub_nonneg.mpr he2)
      (mul_nonneg (norm_nonneg (fderiv ℝ u x)) (norm_nonneg x))]
  have h2 : ‖(Real.exp (u x) - 1) • ContinuousLinearMap.id ℝ V‖ ≤ 1 / 4 := by
    simpa only [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_id, mul_one] using he
  exact (norm_add_le _ _).trans (by linarith)

theorem euclideanGauge_approximates_id {u : V → ℝ} (hu : Differentiable ℝ u)
    (hv : ∀ x, (1 + ‖x‖) * |u x| ≤ 1 / 8)
    (hd : ∀ x, (1 + ‖x‖) * ‖fderiv ℝ u x‖ ≤ 1 / 8) :
    ApproximatesLinearOn (euclideanGauge u) (ContinuousLinearMap.id ℝ V) univ
      (1 / 2 : ℝ≥0) := by
  have hl : LipschitzWith (1 / 2 : ℝ≥0) (fun x => euclideanGauge u x - x) :=
    lipschitzWith_of_nnnorm_fderiv_le
      (fun x => ((euclideanGauge_hasFDerivAt (hu x)).sub (hasFDerivAt_id x)).differentiableAt)
      (fun x => by
        exact_mod_cast euclideanGauge_sub_id_fderiv_bound (hu x) (hv x) (hd x))
  exact hl.lipschitzOnWith.approximatesLinearOn

theorem exists_euclideanGauge_homeomorph {u : V → ℝ} (hu : ContDiff ℝ ∞ u)
    (hv : ∀ x, (1 + ‖x‖) * |u x| ≤ 1 / 8)
    (hd : ∀ x, (1 + ‖x‖) * ‖fderiv ℝ u x‖ ≤ 1 / 8) :
    ∃ e : V ≃ₜ V, (e : V → V) = euclideanGauge u := by
  have hgauge : ContDiff ℝ ∞ (euclideanGauge u) := by
    exact (hu.exp).smul contDiff_id
  have hclose : ∀ x, ‖fderiv ℝ (euclideanGauge u) x -
      ContinuousLinearMap.id ℝ V‖ ≤ 1 / 2 := by
    intro x
    have hbound := euclideanGauge_sub_id_fderiv_bound
      (hu.differentiable (by simp) x) (hv x) (hd x)
    change ‖fderiv ℝ (fun y => euclideanGauge u y - id y) x‖ ≤ 1 / 2 at hbound
    rw [fderiv_fun_sub (hgauge.differentiable (by simp) x) differentiableAt_id,
      fderiv_id] at hbound
    exact hbound
  obtain ⟨e, he, _, _⟩ :=
    Poincare.Analysis.Calculus.exists_smooth_homeomorph_of_fderiv_close_id
      (f := euclideanGauge u) hgauge (by norm_num : (1 / 2 : ℝ≥0) < 1) hclose
  exact ⟨e, he⟩

end PoincareConjecture.M35.RadialGauge
