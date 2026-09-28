import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Index.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace Poincare.ODE.Jacobi

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem IsJacobiSolOn.inner_endpoint_le_hyperbolic_of_index_sub_nonneg
    {R : ℝ → F →L[ℝ] F} {y v : ℝ → F} {C : ℝ}
    (hC : 0 < C) (hsol : IsJacobiSolOn R 0 1 y v)
    (hR : ContinuousOn R (Icc 0 1))
    (hRs : ∀ t, ∀ u w : F, inner ℝ (R t u) w = inner ℝ u (R t w))
    (hRn : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : F,
      -(C ^ 2) * inner ℝ u u ≤ inner ℝ (R t u) u)
    (hy0 : y 0 = 0)
    (hindex : 0 ≤ indexForm R 0 1
      (y - fun t => (Real.sinh (C * t) / Real.sinh C) • y 1)
      (v - fun t => (C * Real.cosh (C * t) / Real.sinh C) • y 1)
      (y - fun t => (Real.sinh (C * t) / Real.sinh C) • y 1)
      (v - fun t => (C * Real.cosh (C * t) / Real.sinh C) • y 1)) :
    inner ℝ (v 1) (y 1) ≤
      (C * Real.cosh C / Real.sinh C) * inner ℝ (y 1) (y 1) := by
  let z : ℝ → F := fun t => (Real.sinh (C * t) / Real.sinh C) • y 1
  let w : ℝ → F := fun t => (C * Real.cosh (C * t) / Real.sinh C) • y 1
  let S : ℝ → F →L[ℝ] F := fun _ => -(C ^ 2) • ContinuousLinearMap.id ℝ F
  have hsinh : Real.sinh C ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hC)
  have hz0 : z 0 = 0 := by simp [z]
  have hz1 : z 1 = y 1 := by simp [z, hsinh]
  have hzd (t : ℝ) : HasDerivAt z (w t) t := by
    convert (((hasDerivAt_id t).const_mul C).sinh.div_const (Real.sinh C)).smul_const
      (y 1) using 1 <;> simp [z, w, mul_comm]
  have hwd (t : ℝ) : HasDerivAt w (-(S t) (z t)) t := by
    convert ((((hasDerivAt_id t).const_mul C).cosh.const_mul C).div_const
      (Real.sinh C)).smul_const (y 1) using 1
    · rfl
    · simp only [z, S, neg_apply, smul_apply,
        ContinuousLinearMap.id_apply, neg_smul, neg_neg, smul_smul, id_eq]
      congr 1
      ring
  have hzc : Continuous z := by dsimp [z]; fun_prop
  have hwc : Continuous w := by dsimp [w]; fun_prop
  have hmodel : IsJacobiSolOn S 0 1 z w :=
    ⟨fun t _ => (hzd t).hasDerivWithinAt, fun t _ => (hwd t).hasDerivWithinAt⟩
  have hint (f f' k k' : ℝ → F)
      (hf : ContinuousOn f (Icc 0 1)) (hf' : ContinuousOn f' (Icc 0 1))
      (hk : ContinuousOn k (Icc 0 1)) (hk' : ContinuousOn k' (Icc 0 1)) :
      IntervalIntegrable (indexIntegrand R f f' k k') volume 0 1 := by
    apply intInt_indexIntegrand <;> rw [uIcc_of_le zero_le_one]
    exacts [hR, hf, hf', hk, hk']
  have hyy := hint y v y v hsol.continuousOn_fst hsol.continuousOn_snd
    hsol.continuousOn_fst hsol.continuousOn_snd
  have hyz := hint y v z w hsol.continuousOn_fst hsol.continuousOn_snd
    hzc.continuousOn hwc.continuousOn
  have hzz := hint z w z w hzc.continuousOn hwc.continuousOn
    hzc.continuousOn hwc.continuousOn
  have hss : IntervalIntegrable (indexIntegrand S z w z w) volume 0 1 :=
    intInt_indexIntegrand continuousOn_const hzc.continuousOn hwc.continuousOn
      hzc.continuousOn hwc.continuousOn
  have hself : indexForm R 0 1 y v y v = inner ℝ (v 1) (y 1) := by
    rw [hsol.indexForm_eq_sub zero_le_one hR hsol.hasDerivWithinAt_fst
      hsol.continuousOn_snd, hy0, inner_zero_right, sub_zero]
  have hcross : indexForm R 0 1 y v z w = inner ℝ (v 1) (y 1) := by
    rw [hsol.indexForm_eq_sub zero_le_one hR
      (fun t _ => (hzd t).hasDerivWithinAt) hwc.continuousOn,
      hz0, hz1, inner_zero_right, sub_zero]
  have hmodelvalue : indexForm S 0 1 z w z w =
      (C * Real.cosh C / Real.sinh C) * inner ℝ (y 1) (y 1) := by
    rw [hmodel.indexForm_eq_sub zero_le_one continuousOn_const
      hmodel.hasDerivWithinAt_fst hwc.continuousOn,
      hz0, hz1, inner_zero_right, sub_zero]
    simp [w, real_inner_smul_left]
  have hexpand := indexForm_add_smul hRs hyy hyz hzz (-1)
  have hdiff : y + (-1 : ℝ) • z = y - z := by
    funext t
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, neg_smul, one_smul]
    simpa only [Pi.sub_apply] using (sub_eq_add_neg (y t) (z t)).symm
  have hdiff' : v + (-1 : ℝ) • w = v - w := by
    funext t
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, neg_smul, one_smul]
    simpa only [Pi.sub_apply] using (sub_eq_add_neg (v t) (w t)).symm
  rw [hdiff, hdiff', hself, hcross] at hexpand
  have hupper : indexForm R 0 1 z w z w ≤
      (C * Real.cosh C / Real.sinh C) * inner ℝ (y 1) (y 1) := by
    rw [← hmodelvalue]
    apply intervalIntegral.integral_mono_on zero_le_one hzz hss
    intro t ht
    have h := hRn t ht (z t)
    simp only [indexIntegrand, S, smul_apply,
      ContinuousLinearMap.id_apply, real_inner_smul_left]
    linarith
  change 0 ≤ indexForm R 0 1 (y - z) (v - w) (y - z) (v - w) at hindex
  linarith

end Poincare.ODE.Jacobi
