import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option autoImplicit false

open Filter
open scoped Topology

namespace PoincareConjecture.M10

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem momentum_time_derivative_of_action
    {E : X × ℝ → Y} {A : X × ℝ → ℝ} {P : X × ℝ → Y →L[ℝ] ℝ}
    {L : ℝ × Y × Y → ℝ} {z₀ : X × ℝ}
    (hE : ContDiffAt ℝ 2 E z₀) (hA : ContDiffAt ℝ 2 A z₀)
    (hP : DifferentiableAt ℝ P z₀)
    (hL : DifferentiableAt ℝ L (z₀.2, E z₀, fderiv ℝ E z₀ (0, 1)))
    (hspace : ∀ᶠ z in 𝓝 z₀, ∀ h : X,
      fderiv ℝ A z (h, 0) = P z (fderiv ℝ E z (h, 0)))
    (htime : ∀ᶠ z in 𝓝 z₀,
      fderiv ℝ A z (0, 1) = L (z.2, E z, fderiv ℝ E z (0, 1)))
    (hvelocity : ∀ v : Y,
      fderiv ℝ L (z₀.2, E z₀, fderiv ℝ E z₀ (0, 1)) (0, 0, v) = P z₀ v)
    (hsurj : Function.Surjective (fun h : X ↦ fderiv ℝ E z₀ (h, 0))) (v : Y) :
    fderiv ℝ P z₀ (0, 1) v =
      fderiv ℝ L (z₀.2, E z₀, fderiv ℝ E z₀ (0, 1)) (0, v, 0) := by
  have hDE : DifferentiableAt ℝ (fderiv ℝ E) z₀ :=
    (hE.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDA : DifferentiableAt ℝ (fderiv ℝ A) z₀ :=
    (hA.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hEvalE (w : X × ℝ) : HasFDerivAt (fun z ↦ fderiv ℝ E z w)
      ((fderiv ℝ (fderiv ℝ E) z₀).flip w) z₀ := by
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using
      hDE.hasFDerivAt.clm_apply (hasFDerivAt_const w z₀)
  have hEvalA (w : X × ℝ) : HasFDerivAt (fun z ↦ fderiv ℝ A z w)
      ((fderiv ℝ (fderiv ℝ A) z₀).flip w) z₀ := by
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using
      hDA.hasFDerivAt.clm_apply (hasFDerivAt_const w z₀)
  obtain ⟨h, rfl⟩ := hsurj v
  let et : X × ℝ := (0, 1)
  let eh : X × ℝ := (h, 0)
  have hS := congrArg (fun D : (X × ℝ) →L[ℝ] ℝ ↦ D et)
    (Filter.EventuallyEq.fderiv_eq (hspace.mono (fun _ hz ↦ hz h)))
  rw [(hEvalA eh).fderiv, (hP.hasFDerivAt.clm_apply (hEvalE eh)).fderiv] at hS
  simp only [ContinuousLinearMap.flip_apply, add_apply,
    ContinuousLinearMap.comp_apply] at hS
  let c : X × ℝ → ℝ × Y × Y := fun z ↦ (z.2, E z, fderiv ℝ E z et)
  have hC : HasFDerivAt c
      ((ContinuousLinearMap.snd ℝ X ℝ).prod
        ((fderiv ℝ E z₀).prod ((fderiv ℝ (fderiv ℝ E) z₀).flip et))) z₀ :=
    hasFDerivAt_snd.prodMk
      ((hE.differentiableAt two_ne_zero).hasFDerivAt.prodMk (hEvalE et))
  have hT := congrArg (fun D : (X × ℝ) →L[ℝ] ℝ ↦ D eh)
    (Filter.EventuallyEq.fderiv_eq htime)
  change fderiv ℝ (fun z ↦ fderiv ℝ A z et) z₀ eh = fderiv ℝ (L ∘ c) z₀ eh at hT
  rw [(hEvalA et).fderiv, (hL.hasFDerivAt.comp z₀ hC).fderiv] at hT
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply] at hT
  have hsplit : ((0 : ℝ), fderiv ℝ E z₀ eh, fderiv ℝ (fderiv ℝ E) z₀ eh et) =
      (0, fderiv ℝ E z₀ eh, 0) + (0, 0, fderiv ℝ (fderiv ℝ E) z₀ eh et) := by
    simp
  change fderiv ℝ (fderiv ℝ A) z₀ eh et =
    fderiv ℝ L (z₀.2, E z₀, fderiv ℝ E z₀ et)
      (0, fderiv ℝ E z₀ eh, fderiv ℝ (fderiv ℝ E) z₀ eh et) at hT
  rw [hsplit, map_add, hvelocity] at hT
  have hAsymm := (hA.isSymmSndFDerivAt (by simp)).eq et eh
  have hEsymm := (hE.isSymmSndFDerivAt (by simp)).eq et eh
  rw [hAsymm, hEsymm] at hS
  change fderiv ℝ P z₀ et (fderiv ℝ E z₀ eh) =
    fderiv ℝ L (z₀.2, E z₀, fderiv ℝ E z₀ et) (0, fderiv ℝ E z₀ eh, 0)
  linarith

end PoincareConjecture.M10
