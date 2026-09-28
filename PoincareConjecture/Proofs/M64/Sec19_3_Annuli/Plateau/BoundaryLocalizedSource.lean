import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundarySourceVariations
import PoincareConjecture.Proofs.M07.Analysis.Calculus.Diffeomorphism.Perturbation
import Mathlib.Analysis.Calculus.Deriv.Support

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal

namespace PoincareConjecture

local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)

private theorem periodic_scalar_bound {f : ℝ → ℝ} (hf : Continuous f)
    (hp : Function.Periodic f curvePeriod) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f x| ≤ C := by
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  obtain ⟨C, hC⟩ := (hp.compact_of_continuous hP.ne' hf).exists_bound_of_continuousOn
    continuousOn_id
  exact ⟨max C 0, le_max_right _ _, fun x => (hC _ (mem_range_self x)).trans (le_max_left _ _)⟩

private theorem compact_scalar_bound {f : ℝ → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hc
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

theorem m64LocalizedHorizontalField_bounded_derivative
    {eta rho : ℝ → ℝ} (heta : ContDiff ℝ ∞ eta)
    (hperiod : Function.Periodic eta curvePeriod)
    (hrho : ContDiff ℝ ∞ rho) (hcompact : HasCompactSupport rho) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : LoopPlane,
      ‖fderiv ℝ (fun q : LoopPlane => (eta (q 0) * rho (q 1)) • e0) p‖ ≤ C := by
  have hdperiod : Function.Periodic (deriv eta) curvePeriod := by
    intro x
    have hfun : (fun y => eta (y + curvePeriod)) = eta := funext hperiod
    simpa only [deriv_comp_add_const] using congrArg (fun f : ℝ → ℝ => deriv f x) hfun
  obtain ⟨B0, hB0, hb0⟩ := periodic_scalar_bound heta.continuous hperiod
  obtain ⟨B1, hB1, hb1⟩ := periodic_scalar_bound (heta.continuous_deriv (by simp)) hdperiod
  obtain ⟨C0, hC0, hc0⟩ := compact_scalar_bound hrho.continuous hcompact
  obtain ⟨C1, hC1, hc1⟩ := compact_scalar_bound (hrho.continuous_deriv (by simp)) hcompact.deriv
  have hproj (i : Fin 2) : ‖(EuclideanSpace.proj i : LoopPlane →L[ℝ] ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simpa only [one_mul, EuclideanSpace.coe_proj] using PiLp.norm_apply_le v i
  refine ⟨B0 * C1 + C0 * B1, by positivity, ?_⟩
  intro p
  have he := (heta.differentiable (by simp) (p 0)).hasDerivAt.comp_hasFDerivAt p
    (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).hasFDerivAt
  have hr := (hrho.differentiable (by simp) (p 1)).hasDerivAt.comp_hasFDerivAt p
    (EuclideanSpace.proj (1 : Fin 2) : LoopPlane →L[ℝ] ℝ).hasFDerivAt
  have hd := (he.mul hr).smul_const e0
  simp only [Pi.mul_apply, Function.comp_def, EuclideanSpace.coe_proj] at hd
  rw [hd.fderiv, ContinuousLinearMap.norm_smulRight_apply]
  have he0 : ‖e0‖ = 1 := by simp
  rw [he0, mul_one]
  calc
    _ ≤ ‖eta (p 0) • (deriv rho (p 1) • (EuclideanSpace.proj (1 : Fin 2)))‖ +
        ‖rho (p 1) • (deriv eta (p 0) • (EuclideanSpace.proj (0 : Fin 2)))‖ := norm_add_le _ _
    _ ≤ B0 * (C1 * 1) + C0 * (B1 * 1) := by
      simp only [norm_smul, Real.norm_eq_abs]
      gcongr
      · exact hb0 _
      · exact hc1 _
      · exact hproj 1
      · exact hc0 _
      · exact hb1 _
      · exact hproj 0
    _ = _ := by ring

theorem m64_exists_smooth_localized_horizontal_source
    {eta rho : ℝ → ℝ} (heta : ContDiff ℝ ∞ eta)
    (hperiod : Function.Periodic eta curvePeriod)
    (hrho : ContDiff ℝ ∞ rho) (hcompact : HasCompactSupport rho) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, |t| < delta →
      ∃ T : LoopPlane ≃ₜ LoopPlane,
        (∀ p, T p = p + t • ((eta (p 0) * rho (p 1)) • e0)) ∧
        ContDiff ℝ ∞ T ∧ ContDiff ℝ ∞ T.symm ∧
        ∀ p, ‖fderiv ℝ T p - ContinuousLinearMap.id ℝ LoopPlane‖ ≤ 1 / 2 := by
  let X := fun p : LoopPlane => (eta (p 0) * rho (p 1)) • e0
  have hX : ContDiff ℝ ∞ X :=
    ((heta.comp (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).contDiff).mul
      (hrho.comp (EuclideanSpace.proj (1 : Fin 2) : LoopPlane →L[ℝ] ℝ).contDiff)).smul
        contDiff_const
  obtain ⟨C, hC, hc⟩ := m64LocalizedHorizontalField_bounded_derivative
    heta hperiod hrho hcompact
  refine ⟨1 / (2 * (C + 1)), by positivity, ?_⟩
  intro t ht
  have htC : |t| * C < 1 / 2 := by
    have hh := (lt_div_iff₀ (show 0 < 2 * (C + 1) by positivity)).mp ht
    nlinarith [abs_nonneg t]
  let f := fun p : LoopPlane => p + t • X p
  have hf : ContDiff ℝ ∞ f := contDiff_id.add (hX.const_smul t)
  have hclose (p : LoopPlane) :
      ‖fderiv ℝ f p - ContinuousLinearMap.id ℝ LoopPlane‖ ≤ (1 / 2 : ℝ≥0) := by
    have hd := (hasFDerivAt_id p).add ((hX.differentiable (by simp) p).hasFDerivAt.const_smul t)
    change HasFDerivAt f (ContinuousLinearMap.id ℝ LoopPlane + t • fderiv ℝ X p) p at hd
    rw [hd.fderiv, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hc p) (abs_nonneg t)).trans htC.le
  obtain ⟨T, hT, hs, hi⟩ :=
    Poincare.Analysis.Calculus.exists_smooth_homeomorph_of_fderiv_close_id hf
      (by norm_num : (1 / 2 : ℝ≥0) < 1) hclose
  exact ⟨T, fun p => congrFun hT p, hs, hi, fun p => by rw [hT]; exact hclose p⟩

end PoincareConjecture
