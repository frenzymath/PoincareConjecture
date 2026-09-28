import PoincareConjecture.Proofs.M60.Mathlib.CauchyTransformKernel
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

open Set Filter MeasureTheory Metric Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M60

private theorem polar_symm_eq_circleMap (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  apply Complex.ext <;>
    simp [Complex.polarCoord_symm_apply, circleMap_zero_re, circleMap_zero_im,
      cos_ofReal_re, sin_ofReal_re]

private theorem radius_smul_cauchyTransformKernel {r : ℝ} (hr : 0 < r)
    (hr3 : r < 3) (θ : ℝ) :
    r • cauchyTransformKernel (circleMap 0 r θ) =
      (Real.pi⁻¹ : ℝ) • (circleMap 0 1 θ)⁻¹ := by
  have hm : circleMap 0 r θ ∈ ball (0 : ℂ) 3 := by
    simpa only [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hr] using hr3
  rw [cauchyTransformKernel, indicator_of_mem hm]
  simp only [circleMap_zero, ofReal_one, one_mul, real_smul, mul_inv_rev]
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  field_simp

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]

theorem cauchyTransform_eq_polar (f : ℂ → V) (z : ℂ) :
    cauchyTransform f z =
      ∫ p in Ioo (0 : ℝ) 3 ×ˢ Ioo (-Real.pi) Real.pi,
        (Real.pi⁻¹ : ℝ) • ((circleMap 0 1 p.2)⁻¹ •
          f (z - circleMap 0 p.1 p.2)) := by
  classical
  let S : Set (ℝ × ℝ) := Iio (3 : ℝ) ×ˢ univ
  have hS : MeasurableSet S := measurableSet_Iio.prod MeasurableSet.univ
  have hset : S ∩ polarCoord.target =
      Ioo (0 : ℝ) 3 ×ˢ Ioo (-Real.pi) Real.pi := by
    ext p
    simp only [S, polarCoord_target, mem_inter_iff, mem_prod, mem_Iio,
      mem_univ, and_true, mem_Ioi, mem_Ioo]
    tauto
  change (∫ w : ℂ, cauchyTransformKernel w • f (z - w)) = _
  rw [← Complex.integral_comp_polarCoord_symm]
  calc
    _ = ∫ p in polarCoord.target,
        S.indicator (fun p => (Real.pi⁻¹ : ℝ) •
          ((circleMap 0 1 p.2)⁻¹ • f (z - circleMap 0 p.1 p.2))) p := by
      apply setIntegral_congr_fun polarCoord.open_target.measurableSet
      intro p hp
      have hr : 0 < p.1 := hp.1
      dsimp only
      rw [polar_symm_eq_circleMap]
      by_cases hs : p ∈ S
      · rw [indicator_of_mem hs, ← smul_assoc,
          radius_smul_cauchyTransformKernel hr hs.1, smul_assoc]
      · have hr3 : ¬p.1 < 3 := fun h => hs ⟨h, mem_univ _⟩
        have hm : circleMap 0 p.1 p.2 ∉ ball (0 : ℂ) 3 := by
          simpa only [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hr] using hr3
        simp [cauchyTransformKernel, indicator_of_notMem hm, indicator_of_notMem hs]
    _ = _ := by rw [integral_indicator hS, Measure.restrict_restrict hS, hset]

omit [IsScalarTower ℝ ℂ V] in

theorem continuous_cauchyTransform_polar {f : ℂ → V} (hf : Continuous f) (z : ℂ) :
    Continuous (fun p : ℝ × ℝ => (Real.pi⁻¹ : ℝ) •
      ((circleMap 0 1 p.2)⁻¹ • f (z - circleMap 0 p.1 p.2))) := by
  simp only [circleMap_zero_inv]
  simp only [inv_one, circleMap_zero]
  fun_prop

theorem cauchyTransform_eq_iterated_polar [CompleteSpace V]
    {f : ℂ → V} (hf : Continuous f) (z : ℂ) :
    cauchyTransform f z =
      ∫ r in (0 : ℝ)..3, ∫ θ in (-Real.pi)..Real.pi,
        (Real.pi⁻¹ : ℝ) • ((circleMap 0 1 θ)⁻¹ •
          f (z - circleMap 0 r θ)) := by
  have hcont := continuous_cauchyTransform_polar hf z
  have hint : IntegrableOn (fun p : ℝ × ℝ => (Real.pi⁻¹ : ℝ) •
      ((circleMap 0 1 p.2)⁻¹ • f (z - circleMap 0 p.1 p.2)))
      (Ioo (0 : ℝ) 3 ×ˢ Ioo (-Real.pi) Real.pi) (volume.prod volume) :=
    (hcont.continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono (Ioo_subset_Icc_self (a := (0 : ℝ)) (b := 3))
        (Ioo_subset_Icc_self (a := -Real.pi) (b := Real.pi)))
  rw [cauchyTransform_eq_polar, Measure.volume_eq_prod,
    setIntegral_prod _ hint,
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 3 by norm_num),
    integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r _
  dsimp only
  rw [intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le),
    integral_Ioc_eq_integral_Ioo]

end PoincareConjecture.M60
