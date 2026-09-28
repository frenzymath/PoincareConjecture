import PoincareConjecture.Proofs.M35.RadialGauge.EuclideanGaugeTime
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

set_option autoImplicit false
set_option maxSynthPendingDepth 5

open Set
open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

private theorem scalar_scale_hessian {S : V → ℝ}
    (hS : ContDiff ℝ ∞ S) (x v w : V) :
    fderiv ℝ (fderiv ℝ (fun y => S y • y)) x v w =
      fderiv ℝ S x v • w + fderiv ℝ S x w • v +
        fderiv ℝ (fderiv ℝ S) x v w • x := by
  let F : V → V := fun y => S y • y
  have hF : ContDiff ℝ ∞ F := hS.smul contDiff_id
  have hf (y : V) : fderiv ℝ F y w =
      S y • w + fderiv ℝ S y w • y := by
    have hd := (hS.differentiable (by simp) y).hasFDerivAt.smul (hasFDerivAt_id y)
    change HasFDerivAt F _ y at hd
    rw [hd.fderiv]
    rfl
  have hleft := ((hF.fderiv_right (m := ∞) (by simp)).differentiable
    (by simp) x).hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have hright := ((hS.differentiable (by simp) x).hasFDerivAt.smul_const w).add
    ((((hS.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt.clm_apply
      (hasFDerivAt_const w x)).smul (hasFDerivAt_id x))
  have heq : (fun y => fderiv ℝ F y w) =
      fun y => S y • w + fderiv ℝ S y w • y := funext hf
  rw [heq] at hleft
  have h := congrArg (fun L : V →L[ℝ] V => L v) (hleft.unique hright)
  simpa only [add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply,
    ContinuousLinearMap.id_apply, id_eq, add_assoc] using h

private theorem exp_hessian {u : V → ℝ} (hu : ContDiff ℝ ∞ u) (x v w : V) :
    fderiv ℝ (fderiv ℝ (fun y => Real.exp (u y))) x v w =
      Real.exp (u x) * (fderiv ℝ (fderiv ℝ u) x v w + fderiv ℝ u x v * fderiv ℝ u x w) := by
  have hd := (contDiff_infty_iff_fderiv.mp hu).2
  have heq : (fun y => fderiv ℝ (fun z => Real.exp (u z)) y w) =
      fun y => Real.exp (u y) * fderiv ℝ u y w := by
    funext y
    rw [((hu.differentiable (by simp) y).hasFDerivAt.exp).fderiv]
    rfl
  have hleft := (((contDiff_infty_iff_fderiv.mp hu.exp).2).differentiable
    (by simp) x).hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have hright := (hu.differentiable (by simp) x).hasFDerivAt.exp.mul
    ((hd.differentiable (by simp) x).hasFDerivAt.clm_apply (hasFDerivAt_const w x))
  rw [heq] at hleft
  have h := congrArg (fun L : V →L[ℝ] ℝ => L v) (hleft.unique hright)
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    zero_apply, map_zero, zero_add, smul_apply, smul_eq_mul] at h
  rw [h]
  ring

theorem euclideanGauge_hessian_apply {u : V → ℝ} (hu : ContDiff ℝ ∞ u) (x v w : V) :
    fderiv ℝ (fderiv ℝ (euclideanGauge u)) x v w =
      (Real.exp (u x) * fderiv ℝ u x v) • w +
        (Real.exp (u x) * fderiv ℝ u x w) • v +
        (Real.exp (u x) * (fderiv ℝ (fderiv ℝ u) x v w +
          fderiv ℝ u x v * fderiv ℝ u x w)) • x := by
  unfold euclideanGauge
  rw [scalar_scale_hessian hu.exp, exp_hessian hu,
    ((hu.differentiable (by simp) x).hasFDerivAt.exp).fderiv]
  rfl

theorem euclideanGauge_hessian_joint_c1
    {u : ℝ → V → ℝ} {J : Set ℝ}
    (hs : ∀ s ∈ J, ContDiff ℝ ∞ (u s))
    (hu : ContDiffOn ℝ 1 (Function.uncurry u) (J ×ˢ univ))
    (hdu : ContDiffOn ℝ 1 (fun p : ℝ × V => fderiv ℝ (u p.1) p.2) (J ×ˢ univ))
    (hddu : ContDiffOn ℝ 1 (fun p : ℝ × V => fderiv ℝ (fderiv ℝ (u p.1)) p.2)
      (J ×ˢ univ)) :
    ContDiffOn ℝ 1 (fun p : ℝ × V => fderiv ℝ (fderiv ℝ (euclideanGauge (u p.1))) p.2)
      (J ×ˢ univ) := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  have hv := hdu.clm_apply (contDiffOn_const (c := v))
  have hw := hdu.clm_apply (contDiffOn_const (c := w))
  have hdd := (hddu.clm_apply (contDiffOn_const (c := v))).clm_apply (contDiffOn_const (c := w))
  apply (((hu.exp.mul hv).smul (contDiffOn_const (c := w))).add
    ((hu.exp.mul hw).smul (contDiffOn_const (c := v)))).add
      ((hu.exp.mul (hdd.add (hv.mul hw))).smul contDiffOn_snd) |>.congr
  intro p hp
  exact euclideanGauge_hessian_apply (hs p.1 hp.1) p.2 v w

end PoincareConjecture.M35.RadialGauge
