


import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff









set_option autoImplicit false

open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Interval

namespace Poincare.Analysis

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem hasDerivAt_intervalIntegral_of_contDiff
    {F : ℝ × ℝ → E} (hF : ContDiff ℝ ∞ F) (a b x : ℝ) :
    HasDerivAt (fun y => ∫ t in a..b, F (y, t))
      (∫ t in a..b, fderiv ℝ F (x, t) (1, 0)) x := by
  let D : ℝ × ℝ → E := fun q => fderiv ℝ F q (1, 0)
  have hD : ContDiff ℝ ∞ D := (hF.fderiv_right (by simp)).clm_apply contDiff_const
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x 1).prod
    (isCompact_uIcc (a := a) (b := b))).exists_bound_of_continuousOn hD.continuous.continuousOn
  have hd (y t : ℝ) : HasDerivAt (fun z => F (z, t)) (D (y, t)) y := by
    exact ((hF.differentiable (by simp)) (y, t)).hasFDerivAt.comp_hasDerivAt y
      ((hasDerivAt_id y).prodMk (hasDerivAt_const y t))
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y t => F (y, t)) (F' := fun y t => D (y, t))
    (bound := fun _ => C) (ball_mem_nhds x zero_lt_one) ?_ ?_ ?_ ?_
    intervalIntegrable_const ?_).2
  · exact Eventually.of_forall fun y =>
      (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  · exact (hD.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Eventually.of_forall fun t ht y hy => hC (y, t)
      ⟨ball_subset_closedBall hy, uIoc_subset_uIcc ht⟩
  · exact Eventually.of_forall fun t _ y _ => hd y t



theorem contDiff_intervalIntegral_of_contDiff
    {F : ℝ × ℝ → E} (hF : ContDiff ℝ ∞ F) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x => ∫ t in a..b, F (x, t)) := by
  apply contDiff_infty.mpr
  intro n
  induction n generalizing F with
  | zero =>
      apply contDiff_zero.mpr
      exact (show Differentiable ℝ (fun x => ∫ t in a..b, F (x, t)) from
        fun x => (hasDerivAt_intervalIntegral_of_contDiff hF a b x).differentiableAt).continuous
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
      refine ⟨fun x => (hasDerivAt_intervalIntegral_of_contDiff hF a b x).differentiableAt,
        by simp, ?_⟩
      have hderiv : deriv (fun x => ∫ t in a..b, F (x, t)) =
          fun x => ∫ t in a..b, fderiv ℝ F (x, t) (1, 0) := by
        funext x
        exact (hasDerivAt_intervalIntegral_of_contDiff hF a b x).deriv
      rw [hderiv]
      exact ih ((hF.fderiv_right (by simp)).clm_apply contDiff_const)



theorem hasFDerivAt_parameter_intervalIntegral_of_contDiff
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F) (a b : ℝ) (x : P) :
    HasFDerivAt (fun y => ∫ t in a..b, F (y, t))
      (∫ t in a..b, (fderiv ℝ F (x, t)).comp (ContinuousLinearMap.inl ℝ P ℝ)) x := by
  let D : P × ℝ → P →L[ℝ] E :=
    fun q => (fderiv ℝ F q).comp (ContinuousLinearMap.inl ℝ P ℝ)
  have hD : ContDiff ℝ ∞ D := (hF.fderiv_right (by simp)).clm_comp contDiff_const
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x 1).prod
    (isCompact_uIcc (a := a) (b := b))).exists_bound_of_continuousOn hD.continuous.continuousOn
  have hd (y : P) (t : ℝ) : HasFDerivAt (fun z => F (z, t)) (D (y, t)) y := by
    exact ((hF.differentiable (by simp)) (y, t)).hasFDerivAt.comp y
      (hasFDerivAt_prodMk_left y t)
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y t => F (y, t)) (F' := fun y t => D (y, t))
    (bound := fun _ => C) (ball_mem_nhds x zero_lt_one)
  · exact Eventually.of_forall fun y =>
      (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  · exact (hD.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Eventually.of_forall fun t ht y hy => hC (y, t)
      ⟨ball_subset_closedBall hy, uIoc_subset_uIcc ht⟩
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun t _ y _ => hd y t




theorem contDiff_parameter_intervalIntegral_of_contDiff
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {V : Type (max u v)} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : P × ℝ → V} (hF : ContDiff ℝ ∞ F) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x => ∫ t in a..b, F (x, t)) := by
  apply contDiff_infty.mpr
  intro n
  induction n generalizing V with
  | zero =>
      apply contDiff_zero.mpr
      exact (show Differentiable ℝ (fun x => ∫ t in a..b, F (x, t)) from
        fun x =>
          (hasFDerivAt_parameter_intervalIntegral_of_contDiff hF a b x).differentiableAt).continuous
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
      refine ⟨fun x =>
        (hasFDerivAt_parameter_intervalIntegral_of_contDiff hF a b x).differentiableAt,
        by simp, ?_⟩
      have hderiv : fderiv ℝ (fun x => ∫ t in a..b, F (x, t)) =
          fun x => ∫ t in a..b,
            (fderiv ℝ F (x, t)).comp (ContinuousLinearMap.inl ℝ P ℝ) := by
        funext x
        exact (hasFDerivAt_parameter_intervalIntegral_of_contDiff hF a b x).fderiv
      rw [hderiv]
      exact ih ((hF.fderiv_right (by simp)).clm_comp contDiff_const)

variable [CompleteSpace E]



theorem dslope_eq_integral_deriv
    {f : ℝ → E} (hf : ContDiff ℝ ∞ f) (a b : ℝ) :
    dslope f a b = ∫ t in (0 : ℝ)..1, deriv f (a + t * (b - a)) := by
  by_cases hba : b = a
  · subst b
    simp [dslope_same]
  apply smul_right_injective E (sub_ne_zero.mpr hba)
  dsimp only
  rw [sub_smul_dslope, ← intervalIntegral.integral_smul]
  symm
  have hd (t : ℝ) : HasDerivAt (fun s => f (a + s * (b - a)))
      ((b - a) • deriv f (a + t * (b - a))) t := by
    simpa only [one_mul, Function.comp_apply] using!
      ((hf.differentiable (by simp)) _).hasDerivAt.scomp t
        (((hasDerivAt_id t).mul_const (b - a)).const_add a)
  have hc : Continuous (fun t => (b - a) • deriv f (a + t * (b - a))) :=
    continuous_const.smul ((contDiff_infty_iff_deriv.mp hf).2.continuous.comp
      (continuous_const.add (continuous_id.mul continuous_const)))
  simpa only [one_mul, zero_mul, add_sub_cancel, add_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      (hc.intervalIntegrable 0 1)



theorem contDiff_dslope {f : ℝ → E} (hf : ContDiff ℝ ∞ f) (a : ℝ) :
    ContDiff ℝ ∞ (dslope f a) := by
  have hF : ContDiff ℝ ∞ (fun q : ℝ × ℝ => deriv f (a + q.2 * (q.1 - a))) :=
    (contDiff_infty_iff_deriv.mp hf).2.comp
      (contDiff_const.add (contDiff_snd.mul (contDiff_fst.sub contDiff_const)))
  have h := contDiff_intervalIntegral_of_contDiff hF 0 1
  have heq : dslope f a = fun b => ∫ t in (0 : ℝ)..1, deriv f (a + t * (b - a)) :=
    funext (dslope_eq_integral_deriv hf a)
  rw [heq]
  exact h



theorem contDiff_dslope_uncurry {f : ℝ → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => dslope f p.1 p.2) := by
  have hparam : ContDiff ℝ ∞
      (fun q : (ℝ × ℝ) × ℝ => q.1.1 + q.2 * (q.1.2 - q.1.1)) := by fun_prop
  have hF : ContDiff ℝ ∞
      (fun q : (ℝ × ℝ) × ℝ => deriv f (q.1.1 + q.2 * (q.1.2 - q.1.1))) :=
    (contDiff_infty_iff_deriv.mp hf).2.comp hparam
  have h := contDiff_parameter_intervalIntegral_of_contDiff hF 0 1
  have heq : (fun p : ℝ × ℝ => dslope f p.1 p.2) =
      fun p => ∫ t in (0 : ℝ)..1, deriv f (p.1 + t * (p.2 - p.1)) := by
    funext p
    exact dslope_eq_integral_deriv hf p.1 p.2
  rw [heq]
  exact h


theorem exists_smooth_increment_factor
    {f : ℝ → E} (hf : ContDiff ℝ ∞ f) (a : ℝ) :
    ∃ g : ℝ → E, ContDiff ℝ ∞ g ∧ g a = deriv f a ∧
      ∀ b, f b - f a = (b - a) • g b :=
  ⟨dslope f a, contDiff_dslope hf a, dslope_same f a,
    fun b => (sub_smul_dslope f a b).symm⟩

end Poincare.Analysis
