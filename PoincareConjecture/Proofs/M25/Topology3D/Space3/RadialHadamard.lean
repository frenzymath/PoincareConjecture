import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.DividedDifferences
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

universe u

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def radialDerivativeAverage (f : E → F) (x : E) : E →L[ℝ] F :=
  ∫ t in (0 : ℝ)..1, fderiv ℝ f (t • x)

@[simp] theorem radialDerivativeAverage_zero [CompleteSpace F] (f : E → F) :
    radialDerivativeAverage f 0 = fderiv ℝ f 0 := by
  simp [radialDerivativeAverage]

variable [FiniteDimensional ℝ E]

theorem radialDerivativeAverage_contDiff (f : E → F) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (radialDerivativeAverage f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  exact Poincare.Analysis.contDiff_parameter_intervalIntegral_of_contDiff
    (hd.comp (contDiff_snd.smul contDiff_fst)) 0 1

variable [CompleteSpace F]

omit [FiniteDimensional ℝ E] in

theorem radialDerivativeAverage_apply (f : E → F) (hf : ContDiff ℝ ∞ f) (x : E) :
    radialDerivativeAverage f x x = f x - f 0 := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hc : Continuous (fun t : ℝ => fderiv ℝ f (t • x)) :=
    hd.continuous.comp (continuous_id.smul continuous_const)
  rw [radialDerivativeAverage,
    ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable 0 1) x]
  have hderiv (t : ℝ) : HasDerivAt (fun s : ℝ => f (s • x))
      (fderiv ℝ f (t • x) x) t := by
    simpa only [one_smul, Function.comp_def, id_eq] using
      ((hf.differentiable (by simp)) (t • x)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).smul_const x)
  simpa only [one_smul, zero_smul] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      ((hc.clm_apply continuous_const).intervalIntegrable 0 1)

theorem fderiv_radialDerivativeAverage_zero (f : E → F) (hf : ContDiff ℝ ∞ f) :
    fderiv ℝ (radialDerivativeAverage f) 0 =
      (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ f) 0 := by
  let D := fderiv ℝ f
  let H : E × ℝ → E →L[ℝ] F := fun p => D (p.2 • p.1)
  have hD : ContDiff ℝ ∞ D := hf.fderiv_right (by simp)
  have hH : ContDiff ℝ ∞ H := hD.comp (contDiff_snd.smul contDiff_fst)
  have hparam := Poincare.Analysis.hasFDerivAt_parameter_intervalIntegral_of_contDiff
    hH 0 1 (0 : E)
  change fderiv ℝ (fun x : E => ∫ t in (0 : ℝ)..1, H (x, t)) 0 = _
  rw [hparam.fderiv]
  have hmap (t : ℝ) : (fderiv ℝ H (0, t)).comp (ContinuousLinearMap.inl ℝ E ℝ) =
      t • fderiv ℝ D 0 := by
    have hdt := (hH.differentiable (by simp) (0, t)).hasFDerivAt.comp (0 : E)
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) (0 : E) t)
    have hds := (hD.differentiable (by simp) (t • (0 : E))).hasFDerivAt.comp (0 : E)
      ((hasFDerivAt_id (0 : E)).const_smul t)
    have hds' : HasFDerivAt (fun x : E => H (x, t))
        (t • fderiv ℝ D 0) (0 : E) := by
      simpa only [H, Function.comp_def, smul_zero, ContinuousLinearMap.comp_smul,
        ContinuousLinearMap.comp_id] using hds
    exact hdt.unique hds'
  simp_rw [hmap]
  rw [intervalIntegral.integral_smul_const, integral_id]
  norm_num [D]

theorem exists_smooth_quadratic_factor (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hzero : fderiv ℝ f 0 = 0) :
    ∃ A : E → E →L[ℝ] E →L[ℝ] F, ContDiff ℝ ∞ A ∧
      A 0 = (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ f) 0 ∧
      ∀ x, A x x x = f x - f 0 := by
  let G := radialDerivativeAverage f
  have hG : ContDiff ℝ ∞ G := radialDerivativeAverage_contDiff f hf
  refine ⟨radialDerivativeAverage G, radialDerivativeAverage_contDiff G hG, ?_, ?_⟩
  · rw [radialDerivativeAverage_zero]
    exact fderiv_radialDerivativeAverage_zero f hf
  · intro x
    have hGzero : G 0 = 0 := (radialDerivativeAverage_zero f).trans hzero
    have h := congrArg (fun L : E →L[ℝ] F => L x)
      (radialDerivativeAverage_apply G hG x)
    simpa only [hGzero, sub_zero, G, radialDerivativeAverage_apply f hf x] using h

end PoincareConjecture.M25.Topology3D
