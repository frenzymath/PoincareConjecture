import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchCauchyDecay
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchGaugeCalculus
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.FourierL2Integral
import Mathlib.Analysis.Complex.Liouville

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter MeasureTheory Complex
open scoped Topology SchwartzMap ContDiff

namespace PoincareConjecture.M65Branch

theorem cauchyOperator_eq_schwartzDbarPotential (h : 𝓢(ℂ, ℂ))
    (hs : HasCompactSupport (h : ℂ → ℂ)) :
    cauchyOperator h = schwartzDbarPotential h := by
  have hC : ContDiff ℝ 1 (cauchyOperator h) :=
    contDiff_cauchyOperator (h.smooth 1) hs
  have hP : ContDiff ℝ 1 (schwartzDbarPotential h) :=
    (contDiff_schwartzDbarPotential h).of_le (by simp)
  have hbar (z : ℂ) : dbar (schwartzDbarPotential h) z = h z := by
    simpa only [dbar, dbarLinear, smul_apply, add_apply,
      ContinuousLinearMap.apply_apply, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      dbar_schwartzDbarPotential h z
  have hhol : Differentiable ℂ (fun z => cauchyOperator h z - schwartzDbarPotential h z) := by
    intro z
    have hCd := hC.differentiable one_ne_zero z
    have hPd := hP.differentiable one_ne_zero z
    apply differentiableAt_complex_of_dbar_eq_zero (hCd.sub hPd)
    change dbarLinear (fderiv ℝ
      (fun w => cauchyOperator h w - schwartzDbarPotential h w) z) = 0
    rw [fderiv_fun_sub hCd hPd, map_sub]
    change dbar (cauchyOperator h) z - dbar (schwartzDbarPotential h) z = 0
    rw [dbar_cauchyOperator (h.smooth 1) hs, hbar, sub_self]
  obtain ⟨R, _, hRs⟩ := hs.isCompact.isBounded.subset_ball_lt 0 (0 : ℂ)
  have hCzero : Tendsto (cauchyOperator h) (cocompact ℂ) (𝓝 0) :=
    tendsto_cauchyOperator_cocompact h.continuous.aestronglyMeasurable
      ((subset_tsupport _).trans (hRs.trans ball_subset_closedBall))
      (fun z => h.norm_le_seminorm ℝ z)
  have hzero : Tendsto (fun z => cauchyOperator h z - schwartzDbarPotential h z)
      (cocompact ℂ) (𝓝 0) := by
    simpa only [sub_self] using hCzero.sub (tendsto_schwartzDbarPotential h)
  funext z
  exact sub_eq_zero.mp (hhol.apply_eq_of_tendsto_cocompact z hzero)

theorem fderiv_cauchyOperator_beurling_ae (h : 𝓢(ℂ, ℂ))
    (hs : HasCompactSupport (h : ℂ → ℂ)) :
    (fun z => fderiv ℝ (cauchyOperator h) z 1) =ᵐ[volume]
      (fun z => h z + beurlingL2 (h.toLp 2 volume) z) ∧
    (fun z => fderiv ℝ (cauchyOperator h) z I) =ᵐ[volume]
      (fun z => I * (beurlingL2 (h.toLp 2 volume) z - h z)) := by
  rw [cauchyOperator_eq_schwartzDbarPotential h hs]
  have hboth : ∀ᵐ z ∂volume,
      fderiv ℝ (schwartzDbarPotential h) z 1 = h z + beurlingL2 (h.toLp 2 volume) z ∧
      fderiv ℝ (schwartzDbarPotential h) z I =
        I * (beurlingL2 (h.toLp 2 volume) z - h z) := by
    filter_upwards [dz_schwartzDbarPotential_beurlingL2_ae h] with z hz
    have hbar := dbar_schwartzDbarPotential h z
    have hx : fderiv ℝ (schwartzDbarPotential h) z 1 =
        h z + beurlingL2 (h.toLp 2 volume) z := by
      calc
        _ = (fderiv ℝ (schwartzDbarPotential h) z 1 +
            I * fderiv ℝ (schwartzDbarPotential h) z I) / 2 +
          (fderiv ℝ (schwartzDbarPotential h) z 1 -
            I * fderiv ℝ (schwartzDbarPotential h) z I) / 2 := by ring
        _ = _ := by rw [hbar, hz]
    refine ⟨hx, ?_⟩
    calc
      _ = I * ((fderiv ℝ (schwartzDbarPotential h) z 1 -
          I * fderiv ℝ (schwartzDbarPotential h) z I) / 2 -
        (fderiv ℝ (schwartzDbarPotential h) z 1 +
          I * fderiv ℝ (schwartzDbarPotential h) z I) / 2) := by
        linear_combination (fderiv ℝ (schwartzDbarPotential h) z I) * I_mul_I
      _ = _ := by rw [hbar, hz]
  exact ⟨hboth.mono fun _ h => h.1, hboth.mono fun _ h => h.2⟩

end PoincareConjecture.M65Branch
