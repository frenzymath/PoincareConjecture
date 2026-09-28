import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerTrace










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter Metric
open scoped Topology SchwartzMap InnerProductSpace ContDiff intervalIntegral

namespace PoincareConjecture

set_option maxHeartbeats 1600000 in





theorem m65C1_disk_trace_bound (f : LoopPlane → ℝ) (hf : ContDiff ℝ 1 f) :
    (∫ t in (-Real.pi)..Real.pi, f (Proofs.M58.angularPoint t) ^ 2) ≤
      3 * (∫ z in loopDiskSet, f z ^ 2) +
        ∑ i : Fin 2, ∫ z in loopDiskSet,
          (fderiv ℝ f z (EuclideanSpace.basisFun (Fin 2) ℝ i)) ^ 2 := by
  let B := EuclideanSpace.basisFun (Fin 2) ℝ
  let X := fun z : LoopPlane => f z ^ 2 • z
  have hX : ContDiff ℝ 1 X := (hf.pow 2).smul contDiff_id
  have hdiv (z : LoopPlane) :
      (∑ i : Fin 2, inner ℝ (fderiv ℝ X z (B i)) (B i)) =
        2 * f z ^ 2 + 2 * f z *
          ∑ i : Fin 2, z i * fderiv ℝ f z (B i) := by
    have hd := ((hf.differentiable one_ne_zero z).hasFDerivAt.pow 2).smul
      (hasFDerivAt_id z)
    rw [show ((fun w => f w ^ 2) • id : LoopPlane → LoopPlane) =
      (fun w => f w ^ 2 • w) from rfl] at hd
    change (∑ i : Fin 2, inner ℝ
      (fderiv ℝ (fun w => f w ^ 2 • w) z (B i)) (B i)) = _
    rw [hd.fderiv]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply,
      smul_apply, ContinuousLinearMap.id_apply, inner_add_left,
      real_inner_smul_left, B.inner_eq_one, mul_one, B,
      EuclideanSpace.inner_basisFun_real, Fin.sum_univ_two, pow_one,
      id_eq, Nat.reduceSub, Nat.cast_ofNat, nsmul_eq_mul]
    ring
  have hflux : (∫ z in loopDiskSet, ∑ i : Fin 2,
      inner ℝ (fderiv ℝ X z (B i)) (B i)) =
        ∫ t in (-Real.pi)..Real.pi, f (Proofs.M58.angularPoint t) ^ 2 := by
    rw [m65Integral_divergence_loopDisk X (fun _ _ => hX.contDiffAt)]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [X, real_inner_smul_left, real_inner_self_eq_norm_sq,
      Proofs.M58.norm_angularPoint, one_pow, mul_one]
  have hdcont (i : Fin 2) : Continuous
      (fun z => fderiv ℝ f z (B i)) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hfI : IntegrableOn (fun z => f z ^ 2) loopDiskSet volume :=
    (hf.continuous.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : LoopPlane) 1)
  have hdI (i : Fin 2) : IntegrableOn
      (fun z => (fderiv ℝ f z (B i)) ^ 2) loopDiskSet volume :=
    ((hdcont i).pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : LoopPlane) 1)
  have hDI : IntegrableOn (fun z => 2 * f z ^ 2 + 2 * f z *
      ∑ i : Fin 2, z i * fderiv ℝ f z (B i)) loopDiskSet volume := by
    have hc : Continuous (fun z => 2 * f z ^ 2 + 2 * f z *
        ∑ i : Fin 2, z i * fderiv ℝ f z (B i)) :=
      ((continuous_const.mul (hf.continuous.pow 2)).add
      ((continuous_const.mul hf.continuous).mul
        (continuous_finsetSum _ fun i _ =>
          (EuclideanSpace.proj i).continuous.mul (hdcont i))))
    exact hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : LoopPlane) 1)
  have hbound (z : LoopPlane) (hz : z ∈ loopDiskSet) :
      2 * f z ^ 2 + 2 * f z * ∑ i : Fin 2, z i * fderiv ℝ f z (B i) ≤
        3 * f z ^ 2 + ∑ i : Fin 2, (fderiv ℝ f z (B i)) ^ 2 := by
    have hzNorm : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    have hzSq : (z 0) ^ 2 + (z 1) ^ 2 ≤ 1 := by
      have hnorm := sq_le_sq₀ (norm_nonneg z) zero_le_one |>.mpr hzNorm
      simpa only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two,
        Real.norm_eq_abs, sq_abs, one_pow] using hnorm
    have h0 := sq_nonneg (f z * z 0 - fderiv ℝ f z (B 0))
    have h1 := sq_nonneg (f z * z 1 - fderiv ℝ f z (B 1))
    have hprod := mul_nonneg (sq_nonneg (f z)) (sub_nonneg.mpr hzSq)
    simp only [Fin.sum_univ_two]
    nlinarith
  rw [← hflux]
  calc
    _ = ∫ z in loopDiskSet, 2 * f z ^ 2 + 2 * f z *
        ∑ i : Fin 2, z i * fderiv ℝ f z (B i) := by
      apply setIntegral_congr_fun measurableSet_closedBall
      exact fun z _ => hdiv z
    _ ≤ ∫ z in loopDiskSet, 3 * f z ^ 2 +
        ∑ i : Fin 2, (fderiv ℝ f z (B i)) ^ 2 := by
      apply integral_mono_ae hDI
        ((hfI.const_mul 3).add (integrable_finsetSum _ fun i _ => hdI i))
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
      exact hbound z hz
    _ = _ := by
      rw [integral_add (hfI.const_mul 3) (integrable_finsetSum _ fun i _ => hdI i),
        integral_const_mul, integral_finsetSum _ fun i _ => hdI i]

end PoincareConjecture
