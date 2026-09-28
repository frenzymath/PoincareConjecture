import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Index.Basic

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace Poincare.ODE.Jacobi

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem IsJacobiSolOn.inner_endpoint_le_of_index_sub_nonneg
    {R : ℝ → F →L[ℝ] F} {y v : ℝ → F}
    (hsol : IsJacobiSolOn R 0 1 y v)
    (hR : ContinuousOn R (Icc 0 1))
    (hRs : ∀ t, ∀ u w : F, inner ℝ (R t u) w = inner ℝ u (R t w))
    (hRn : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : F, 0 ≤ inner ℝ (R t u) u)
    (hy0 : y 0 = 0)
    (hindex : 0 ≤ indexForm R 0 1
      (y - fun t => t • y 1) (v - fun _ => y 1)
      (y - fun t => t • y 1) (v - fun _ => y 1)) :
    inner ℝ (v 1) (y 1) ≤ inner ℝ (y 1) (y 1) := by
  let z : ℝ → F := fun t => t • y 1
  let w : ℝ → F := fun _ => y 1
  have hzd (t : ℝ) : HasDerivAt z (w t) t := by
    simpa only [z, w, id_eq, one_smul] using
      (hasDerivAt_id t).smul_const (y 1)
  have hzc : Continuous z := continuous_id.smul continuous_const
  have hwc : Continuous w := continuous_const
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
  have hself : indexForm R 0 1 y v y v = inner ℝ (v 1) (y 1) := by
    rw [hsol.indexForm_eq_sub zero_le_one hR hsol.hasDerivWithinAt_fst
      hsol.continuousOn_snd, hy0, inner_zero_right, sub_zero]
  have hcross : indexForm R 0 1 y v z w = inner ℝ (v 1) (y 1) := by
    rw [hsol.indexForm_eq_sub zero_le_one hR
      (fun t _ => (hzd t).hasDerivWithinAt) hwc.continuousOn]
    simp [z]
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
  have hupper : indexForm R 0 1 z w z w ≤ inner ℝ (y 1) (y 1) := by
    calc
      _ ≤ ∫ _t in (0 : ℝ)..1, inner ℝ (y 1) (y 1) := by
        apply intervalIntegral.integral_mono_on zero_le_one hzz
          (intervalIntegrable_const)
        intro t ht
        exact sub_le_self _ (hRn t ht (z t))
      _ = _ := by simp
  change 0 ≤ indexForm R 0 1 (y - z) (v - w) (y - z) (v - w) at hindex
  linarith

end Poincare.ODE.Jacobi
