import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Tactic

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ContDiff Topology intervalIntegral

namespace PoincareConjecture.M65

theorem exists_periodic_arclength_reparam {v : ℝ → ℝ} {P : ℝ}
    (hv : ContDiff ℝ ∞ v) (hv0 : ∀ x, 0 < v x)
    (hP : 0 < P) (hperiod : Function.Periodic v P) :
    ∃ phi : ℝ ≃o ℝ, phi 0 = 0 ∧
      (∀ x, phi (x + P) = phi x + P) ∧
      ContDiff ℝ ∞ (phi : ℝ → ℝ) ∧
      (∀ x, HasDerivAt (phi : ℝ → ℝ)
        ((∫ y in (0 : ℝ)..P, v y) / (P * v (phi x))) x) ∧
      (∀ x, 0 < deriv (phi : ℝ → ℝ) x) ∧
      ∀ x, deriv (phi : ℝ → ℝ) x * v (phi x) = (∫ y in (0 : ℝ)..P, v y) / P := by
  let L := ∫ y in (0 : ℝ)..P, v y
  have hL : 0 < L := intervalIntegral.intervalIntegral_pos_of_pos
    (hv.continuous.intervalIntegrable _ _) hv0 hP
  let tau : ℝ → ℝ := fun x => P / L * ∫ y in (0 : ℝ)..x, v y
  have htau_deriv (x : ℝ) : HasDerivAt tau (P / L * v x) x :=
    (intervalIntegral.integral_hasDerivAt_right (hv.continuous.intervalIntegrable 0 x)
      hv.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hv.continuous.continuousAt).const_mul (P / L)
  have htau_pos (x : ℝ) : 0 < P / L * v x := mul_pos (div_pos hP hL) (hv0 x)
  have htau_cont : Continuous tau := continuous_iff_continuousAt.mpr
    (fun x => (htau_deriv x).continuousAt)
  have htau_smooth : ContDiff ℝ ∞ tau := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun x => (htau_deriv x).differentiableAt, ?_⟩
    rw [show deriv tau = (fun x => P / L * v x) from funext (fun x => (htau_deriv x).deriv)]
    exact contDiff_const.mul hv
  have htau_mono : StrictMono tau := strictMono_of_hasDerivAt_pos htau_deriv htau_pos
  have htau_surj : Function.Surjective tau :=
    htau_cont.surjective
      ((hperiod.tendsto_atTop_intervalIntegral_of_pos hL hP).const_mul_atTop (div_pos hP hL))
      ((hperiod.tendsto_atBot_intervalIntegral_of_pos hL hP).const_mul_atBot (div_pos hP hL))
  let S : ℝ ≃o ℝ := htau_mono.orderIsoOfSurjective tau htau_surj
  let phi : ℝ ≃o ℝ := S.symm
  have htau_phi (x : ℝ) : tau (phi x) = x := S.apply_symm_apply x
  have htau_zero : tau 0 = 0 := by simp [tau]
  have htau_period (x : ℝ) : tau (x + P) = tau x + P := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hv.continuous.intervalIntegrable 0 x) (hv.continuous.intervalIntegrable x (x + P))
    have hshift := hperiod.intervalIntegral_add_eq x 0
    rw [zero_add] at hshift
    dsimp only [tau]
    rw [← hadd, hshift, mul_add]
    change P / L * (∫ y in (0 : ℝ)..x, v y) + P / L * L = _
    field_simp [hL.ne']
  have hphi_zero : phi 0 = 0 := by
    apply S.injective
    change tau (phi 0) = tau 0
    rw [htau_phi, htau_zero]
  have hphi_period (x : ℝ) : phi (x + P) = phi x + P := by
    apply S.injective
    change tau (phi (x + P)) = tau (phi x + P)
    rw [htau_phi, htau_period, htau_phi]
  have hphi_smooth : ContDiff ℝ ∞ (phi : ℝ → ℝ) :=
    S.toHomeomorph.contDiff_symm_deriv (fun x => (htau_pos x).ne') htau_deriv htau_smooth
  have hphi_deriv (x : ℝ) : HasDerivAt (phi : ℝ → ℝ) (L / (P * v (phi x))) x := by
    have hinverse := (htau_deriv (phi x)).of_local_left_inverse
      phi.continuous.continuousAt (htau_pos (phi x)).ne'
      (Eventually.of_forall htau_phi)
    apply hinverse.congr_deriv
    field_simp
  refine ⟨phi, hphi_zero, hphi_period, hphi_smooth, hphi_deriv, ?_, ?_⟩
  · intro x
    rw [(hphi_deriv x).deriv]
    exact div_pos hL (mul_pos hP (hv0 (phi x)))
  · intro x
    rw [(hphi_deriv x).deriv]
    change L / (P * v (phi x)) * v (phi x) = L / P
    field_simp [(hv0 (phi x)).ne']

end PoincareConjecture.M65
