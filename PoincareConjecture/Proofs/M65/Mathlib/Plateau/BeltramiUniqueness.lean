import PoincareConjecture.Proofs.M65.Mathlib.Plateau.BeltramiNormalization
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.Liouville

set_option autoImplicit false

noncomputable section

open Filter
open scoped Topology ContDiff ComplexConjugate

namespace Complex

private theorem linear_beltrami_formula (L : ℂ →L[ℝ] ℂ) (μ : ℂ)
    (heq : L 1 + I * L I = μ * (L 1 - I * L I)) (v : ℂ) :
    L v = ((L 1 - I * L I) / 2) * (v + μ * conj v) := by
  let p := (L 1 - I * L I) / 2
  change L v = p * (v + μ * conj v)
  have h1 : L 1 = p * (1 + μ) := by
    dsimp [p]
    linear_combination (1 / 2 : ℂ) * heq
  have hI : L I = p * (I - μ * I) := by
    dsimp [p]
    have hh := congrArg (fun a : ℂ => I * a) heq
    simp only [mul_add, mul_sub, ← mul_assoc, I_mul_I, neg_one_mul] at hh
    linear_combination (norm := ring_nf) (-1 / 2 : ℂ) * hh
    simp only [I_sq]
    ring
  have hv : v = v.re • (1 : ℂ) + v.im • I := by
    simp only [real_smul, mul_one, re_add_im]
  conv_lhs => rw [hv, map_add, map_smul, map_smul, h1, hI]
  conv_rhs => rw [hv]
  simp only [real_smul, map_add, map_mul, conj_ofReal, conj_I, mul_one]
  ring

theorem linearMap_beltrami_formula (L : ℂ →L[ℝ] ℂ) (μ : ℂ)
    (heq : L 1 + I * L I = μ * (L 1 - I * L I)) (v : ℂ) :
    L v = ((L 1 - I * L I) / 2) * (v + μ * conj v) :=
  linear_beltrami_formula L μ heq v

private theorem beltrami_transition_hasDerivAt (f g : ℂ ≃ₜ ℂ) (μ : ℂ → ℂ)
    (hf : Differentiable ℝ (f : ℂ → ℂ)) (hfi : Differentiable ℝ (f.symm : ℂ → ℂ))
    (hg : Differentiable ℝ (g : ℂ → ℂ))
    (hfeq : ∀ z, fderiv ℝ (f : ℂ → ℂ) z 1 + I * fderiv ℝ (f : ℂ → ℂ) z I =
      μ z * (fderiv ℝ (f : ℂ → ℂ) z 1 - I * fderiv ℝ (f : ℂ → ℂ) z I))
    (hgeq : ∀ z, fderiv ℝ (g : ℂ → ℂ) z 1 + I * fderiv ℝ (g : ℂ → ℂ) z I =
      μ z * (fderiv ℝ (g : ℂ → ℂ) z 1 - I * fderiv ℝ (g : ℂ → ℂ) z I)) (z : ℂ) :
    HasDerivAt (fun y => g (f.symm y))
      (((fderiv ℝ (g : ℂ → ℂ) (f.symm z) 1 -
          I * fderiv ℝ (g : ℂ → ℂ) (f.symm z) I) / 2) /
        ((fderiv ℝ (f : ℂ → ℂ) (f.symm z) 1 -
          I * fderiv ℝ (f : ℂ → ℂ) (f.symm z) I) / 2)) z := by
  let A := fderiv ℝ (f : ℂ → ℂ) (f.symm z)
  let B := fderiv ℝ (g : ℂ → ℂ) (f.symm z)
  let J := fderiv ℝ (f.symm : ℂ → ℂ) z
  let p := (A 1 - I * A I) / 2
  let q := (B 1 - I * B I) / 2
  have hA (v : ℂ) : A v = p * (v + μ (f.symm z) * conj v) :=
    linear_beltrami_formula A _ (hfeq _) v
  have hB (v : ℂ) : B v = q * (v + μ (f.symm z) * conj v) :=
    linear_beltrami_formula B _ (hgeq _) v
  have hAJ : A.comp J = ContinuousLinearMap.id ℝ ℂ := by
    have hh := ((hf (f.symm z)).hasFDerivAt.comp z (hfi z).hasFDerivAt).fderiv
    simpa only [Function.comp_def, f.apply_symm_apply, fderiv_fun_id] using hh.symm
  have hAJv (v : ℂ) : A (J v) = v := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hAJ
  have hp : p ≠ 0 := by
    intro hp
    have hh := hAJv 1
    rw [hA, hp, zero_mul] at hh
    exact zero_ne_one hh
  have hBJ : B.comp J = (q / p) • ContinuousLinearMap.id ℝ ℂ := by
    ext v
    change B (J v) = (q / p) * v
    calc
      _ = q * (J v + μ (f.symm z) * conj (J v)) := hB _
      _ = (q / p) * (p * (J v + μ (f.symm z) * conj (J v))) := by field_simp
      _ = _ := by rw [← hA, hAJv]
  have hreal : HasFDerivAt (fun y => g (f.symm y))
      ((q / p) • ContinuousLinearMap.id ℝ ℂ) z := by
    convert! ((hg (f.symm z)).hasFDerivAt.comp z (hfi z).hasFDerivAt) using 1
    exact hBJ.symm
  have hcomplex := hreal.complexOfReal_hasFDerivAt (by
    change (q / p) * I = I * ((q / p) * 1)
    ring)
  have hh : HasDerivAt (fun y => g (f.symm y)) (q / p) z := by
    convert! hcomplex.hasDerivAt using 1
    change q / p = (q / p) * 1
    exact (mul_one _).symm
  exact hh

theorem normalized_smooth_beltrami_unique (f g : ℂ ≃ₜ ℂ) (μ : ℂ → ℂ)
    (hf : ContDiff ℝ ∞ (f : ℂ → ℂ)) (hfi : ContDiff ℝ ∞ (f.symm : ℂ → ℂ))
    (hg : ContDiff ℝ ∞ (g : ℂ → ℂ))
    (hf0 : f 0 = 0) (hf1 : f 1 = 1) (hg0 : g 0 = 0) (hg1 : g 1 = 1)
    {a b : ℂ} (ha : a ≠ 0)
    (hflim : Tendsto (fderiv ℝ (f : ℂ → ℂ)) (cocompact ℂ)
      (𝓝 (a • ContinuousLinearMap.id ℝ ℂ)))
    (hglim : Tendsto (fderiv ℝ (g : ℂ → ℂ)) (cocompact ℂ)
      (𝓝 (b • ContinuousLinearMap.id ℝ ℂ)))
    (hfeq : ∀ z, fderiv ℝ (f : ℂ → ℂ) z 1 + I * fderiv ℝ (f : ℂ → ℂ) z I =
      μ z * (fderiv ℝ (f : ℂ → ℂ) z 1 - I * fderiv ℝ (f : ℂ → ℂ) z I))
    (hgeq : ∀ z, fderiv ℝ (g : ℂ → ℂ) z 1 + I * fderiv ℝ (g : ℂ → ℂ) z I =
      μ z * (fderiv ℝ (g : ℂ → ℂ) z 1 - I * fderiv ℝ (g : ℂ → ℂ) z I)) : f = g := by
  let H : ℂ → ℂ := fun z => g (f.symm z)
  have hd := beltrami_transition_hasDerivAt f g μ
    (hf.differentiable (by simp)) (hfi.differentiable (by simp))
    (hg.differentiable (by simp)) hfeq hgeq
  have hH : Differentiable ℂ H := fun z => (hd z).differentiableAt
  have hlinear (c : ℂ) :
      (((c • ContinuousLinearMap.id ℝ ℂ) 1 - I * (c • ContinuousLinearMap.id ℝ ℂ) I) / 2) = c := by
    change (c * 1 - I * (c * I)) / 2 = c
    ring_nf
    simp only [I_sq]
    ring
  have hlimit (u : ℂ → ℂ) (c : ℂ)
      (hl : Tendsto (fderiv ℝ u) (cocompact ℂ) (𝓝 (c • ContinuousLinearMap.id ℝ ℂ))) :
      Tendsto (fun z => (fderiv ℝ u z 1 - I * fderiv ℝ u z I) / 2)
        (cocompact ℂ) (𝓝 c) := by
    have h1 : Tendsto (fun z => fderiv ℝ u z 1) (cocompact ℂ)
        (𝓝 ((c • ContinuousLinearMap.id ℝ ℂ) 1)) :=
      ((continuous_eval_const (1 : ℂ)).tendsto _).comp hl
    have hI : Tendsto (fun z => fderiv ℝ u z I) (cocompact ℂ)
        (𝓝 ((c • ContinuousLinearMap.id ℝ ℂ) I)) :=
      ((continuous_eval_const I).tendsto _).comp hl
    simpa only [hlinear] using (h1.sub (hI.const_mul I)).div_const 2
  have hderivlim : Tendsto (deriv H) (cocompact ℂ) (𝓝 (b / a)) := by
    have hh := ((hlimit _ b hglim).div (hlimit _ a hflim) ha).comp
      f.symm.isClosedEmbedding.tendsto_cocompact
    convert! hh using 1
    funext z
    exact (hd z).deriv
  have hconstant (z : ℂ) : deriv H z = b / a :=
    hH.deriv.apply_eq_of_tendsto_cocompact z hderivlim
  have hzero : f.symm 0 = 0 := f.injective (by simpa only [f.apply_symm_apply] using hf0.symm)
  have hone : f.symm 1 = 1 := f.injective (by simpa only [f.apply_symm_apply] using hf1.symm)
  have haffine (z : ℂ) : H z = (b / a) * z := by
    have hdiff (x : ℂ) : HasDerivAt (fun y => H y - (b / a) * y) 0 x := by
      convert! (hH x).hasDerivAt.sub ((hasDerivAt_id x).const_mul (b / a)) using 1
      simp only [hconstant, mul_one, sub_self]
    have hh := is_const_of_deriv_eq_zero
      (fun x => (hdiff x).differentiableAt) (fun x => (hdiff x).deriv) z 0
    exact sub_eq_zero.mp (by simpa only [H, hzero, hg0, mul_zero, sub_zero] using hh)
  have hratio : b / a = 1 := by
    have hh := haffine 1
    simpa only [H, hone, hg1, mul_one] using hh.symm
  apply Homeomorph.ext
  intro z
  have hh := haffine (f z)
  simpa only [H, f.symm_apply_apply, hratio, one_mul] using hh.symm

end Complex
