import PoincareConjecture.Proofs.M60.Mathlib.CauchyTransformRightInverse
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Operator.Banach










set_option autoImplicit false

open Complex Filter Set
open scoped Topology ContDiff

namespace PoincareConjecture.M60

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]




theorem differentiableAt_complex_of_cauchyRiemannDerivative_eq_zero
    {f : ℂ → V} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hzero : cauchyRiemannDerivative f z = 0) : DifferentiableAt ℂ f z := by
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  refine ⟨hf, ?_⟩
  have hsum : fderiv ℝ f z 1 + I • fderiv ℝ f z I = 0 :=
    (smul_eq_zero.mp hzero).resolve_left (by norm_num)
  have hI := congrArg (fun v : V => I • v) hsum
  simp only [smul_add, smul_smul, I_mul_I, neg_one_smul, smul_zero] at hI
  exact (eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hI)).symm




theorem cauchyRiemannDerivative_apply {A : ℂ → V →L[ℂ] V} {v : ℂ → V} {z : ℂ}
    (hA : DifferentiableAt ℝ A z) (hv : DifferentiableAt ℝ v z) :
    cauchyRiemannDerivative (fun w => A w (v w)) z =
      cauchyRiemannDerivative A z (v z) + A z (cauchyRiemannDerivative v z) := by
  let R := ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ
  have h := (R.hasFDerivAt.comp z hA.hasFDerivAt).clm_apply hv.hasFDerivAt
  change HasFDerivAt (fun w => A w (v w)) _ z at h
  have hd (d : ℂ) : fderiv ℝ (fun w => A w (v w)) z d =
      A z (fderiv ℝ v z d) + fderiv ℝ A z d (v z) := by
    rw [h.fderiv]
    rfl
  have hr (a : ℝ) (w : V) : A z (a • w) = a • A z w :=
    ((A z).restrictScalars ℝ).map_smul a w
  simp only [cauchyRiemannDerivative, hd, smul_add, add_apply,
    smul_apply, map_add, hr, map_smul]
  abel

variable [CompleteSpace V]




theorem differentiableAt_frame_inverse_apply
    {P A : ℂ → V →L[ℂ] V} {v : ℂ → V} {z : ℂ}
    (hP : DifferentiableAt ℝ P z) (hv : DifferentiableAt ℝ v z)
    (hunit : ∀ᶠ w in 𝓝 z, IsUnit (P w))
    (hPeq : cauchyRiemannDerivative P z = A z * P z)
    (hveq : cauchyRiemannDerivative v z = A z (v z)) :
    DifferentiableAt ℂ (fun w => Ring.inverse (P w) (v w)) z := by
  let H : ℂ → V := fun w => Ring.inverse (P w) (v w)
  let R := ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ
  have hPunit : IsUnit (P z) := hunit.self_of_nhds
  have hH : DifferentiableAt ℝ H z :=
    (R.differentiableAt.comp z (hP.inverse hPunit)).clm_apply hv
  apply differentiableAt_complex_of_cauchyRiemannDerivative_eq_zero hH
  have he : (fun w => P w (H w)) =ᶠ[𝓝 z] v := by
    filter_upwards [hunit] with w hw
    have h := congrArg (fun L : V →L[ℂ] V => L (v w)) (Ring.mul_inverse_cancel _ hw)
    exact h
  have hderiv : cauchyRiemannDerivative (fun w => P w (H w)) z =
      cauchyRiemannDerivative v z := by
    simp only [cauchyRiemannDerivative, he.fderiv_eq]
  rw [cauchyRiemannDerivative_apply hP hH, hPeq, hveq] at hderiv
  have hz : P z (H z) = v z := he.eq_of_nhds
  change A z (P z (H z)) + P z (cauchyRiemannDerivative H z) = A z (v z) at hderiv
  rw [hz] at hderiv
  have hzero : P z (cauchyRiemannDerivative H z) = 0 := by
    exact add_left_cancel (hderiv.trans (add_zero _).symm)
  exact (ContinuousLinearMap.isUnit_iff_bijective.mp hPunit).1
    (hzero.trans (map_zero _).symm)




theorem analyticAt_frame_inverse_apply
    {P A : ℂ → V →L[ℂ] V} {v : ℂ → V} {U : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U)
    (hP : ContDiffOn ℝ 1 P U) (hv : ContDiffOn ℝ 1 v U)
    (hunit : ∀ w ∈ U, IsUnit (P w))
    (hPeq : ∀ w ∈ U, cauchyRiemannDerivative P w = A w * P w)
    (hveq : ∀ w ∈ U, cauchyRiemannDerivative v w = A w (v w)) :
    AnalyticAt ℂ (fun w => Ring.inverse (P w) (v w)) z := by
  apply DifferentiableOn.analyticAt (s := U) _ (hU.mem_nhds hz)
  intro w hw
  apply DifferentiableAt.differentiableWithinAt
  exact differentiableAt_frame_inverse_apply
    ((hP.contDiffAt (hU.mem_nhds hw)).differentiableAt (by simp))
    ((hv.contDiffAt (hU.mem_nhds hw)).differentiableAt (by simp))
    (Filter.mem_of_superset (hU.mem_nhds hw) fun x hx => hunit x hx)
    (hPeq w hw) (hveq w hw)




theorem eventually_zero_or_isolated_of_frame
    {P A : ℂ → V →L[ℂ] V} {v : ℂ → V} {U : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U)
    (hP : ContDiffOn ℝ 1 P U) (hv : ContDiffOn ℝ 1 v U)
    (hunit : ∀ w ∈ U, IsUnit (P w))
    (hPeq : ∀ w ∈ U, cauchyRiemannDerivative P w = A w * P w)
    (hveq : ∀ w ∈ U, cauchyRiemannDerivative v w = A w (v w)) :
    (∀ᶠ w in 𝓝 z, v w = 0) ∨ ∀ᶠ w in 𝓝[≠] z, v w ≠ 0 := by
  have han := analyticAt_frame_inverse_apply hU hz hP hv hunit hPeq hveq
  rcases han.eventually_eq_zero_or_eventually_ne_zero with hzero | hiso
  · left
    filter_upwards [hzero, hU.mem_nhds hz] with w hw hwU
    have he := congrArg (fun L : V →L[ℂ] V => L (v w))
      (Ring.mul_inverse_cancel (P w) (hunit w hwU))
    change P w (Ring.inverse (P w) (v w)) = v w at he
    rw [hw, map_zero] at he
    exact he.symm
  · right
    filter_upwards [hiso] with w hw hvw
    exact hw (by rw [hvw, map_zero])

end PoincareConjecture.M60
