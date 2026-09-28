import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityAveragingValue
import PoincareConjecture.Proofs.M03.Existence.DeTurckDomainRegularityNative










set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology ContDiff Convolution SchwartzMap InnerProductSpace LineDeriv

namespace PoincareConjecture.M65Interior

private theorem averagingTest_compact {r : ℝ} (hr : 0 < r) (x : LoopPlane) :
    HasCompactSupport (fun z => averagingKernel r (x - z)) := by
  apply HasCompactSupport.intro (isCompact_closedBall x r)
  intro z hz
  by_contra hne
  apply hz
  rw [mem_closedBall_iff_norm']
  exact mem_closedBall_zero_iff.mp (averagingKernel_support hr hne)

private noncomputable def averagingTest {r : ℝ} (hr : 0 < r) (x : LoopPlane) :
    𝓢(LoopPlane, ℝ) :=
  (averagingTest_compact hr x).toSchwartzMap
    ((averagingKernel_contDiff r).comp (by fun_prop))

private noncomputable def averagingRadiusTest {r : ℝ} (hr : 0 < r)
    (x : LoopPlane) (i : Fin 2) : 𝓢(LoopPlane, ℝ) :=
  ((averagingTest_compact hr x).mul_left
    (f := fun z : LoopPlane => (x i - z i) / r)).toSchwartzMap
      ((by fun_prop : ContDiff ℝ ∞ (fun z : LoopPlane => (x i - z i) / r)).mul
        ((averagingKernel_contDiff r).comp (by fun_prop)))

private theorem averagingTest_fderiv {r : ℝ} (hr : 0 < r) (x z v : LoopPlane) :
    fderiv ℝ (averagingTest hr x) z v = -fderiv ℝ (averagingKernel r) (x - z) v := by
  have hk : DifferentiableAt ℝ (averagingKernel r) (x - z) :=
    ((averagingKernel_contDiff r).differentiable (by simp)) (x - z)
  have ha : HasFDerivAt (fun y : LoopPlane => x - y)
      (0 - ContinuousLinearMap.id ℝ LoopPlane) z :=
    (hasFDerivAt_const x z).sub (hasFDerivAt_id z)
  have hd := hk.hasFDerivAt.comp z ha
  change HasFDerivAt (averagingTest hr x) _ z at hd
  rw [hd.fderiv]
  simp




theorem averagingValue_fderiv_of_weak
    (u : Lp ℝ 2 (volume : Measure LoopPlane))
    (d : Fin 2 → Lp ℝ 2 (volume : Measure LoopPlane))
    (hw : ∀ i (φ : 𝓢(LoopPlane, ℝ)),
      ⟪d i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u z * fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i)))
    {r : ℝ} (hr : 0 < r) (x : LoopPlane) (i : Fin 2) :
    fderiv ℝ (averagingValue u r) x (EuclideanSpace.basisFun (Fin 2) ℝ i) =
      ∫ z, averagingKernel r (x - z) * d i z := by
  have hu := (Lp.memLp u).locallyIntegrable (by norm_num)
  have hk := averagingKernel_contDiff r
  have hc := averagingKernel_hasCompactSupport hr
  have hd := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hu
    (hk.of_le (by simp)) x
  change HasFDerivAt (averagingValue u r) _ x at hd
  have hint := (hc.fderiv ℝ).convolutionExists_right
    ((ContinuousLinearMap.mul ℝ ℝ).precompR LoopPlane) hu
    (hk.continuous_fderiv (by simp)) x
  rw [hd.fderiv, convolution, ContinuousLinearMap.integral_apply hint]
  change (∫ z, u z * fderiv ℝ (averagingKernel r) (x - z)
    (EuclideanSpace.basisFun (Fin 2) ℝ i)) = _
  have h := hw i (averagingTest hr x)
  rw [DeTurckDomainRegularityNative.inner_schwartz] at h
  simp only [averagingTest_fderiv, mul_neg, integral_neg, neg_neg] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards with z
  change d i z * averagingKernel r (x - z) = _
  ring





theorem averagingValue_radius_of_weak
    (u : Lp ℝ 2 (volume : Measure LoopPlane))
    (d : Fin 2 → Lp ℝ 2 (volume : Measure LoopPlane))
    (hw : ∀ i (φ : 𝓢(LoopPlane, ℝ)),
      ⟪d i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u z * fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i)))
    {r : ℝ} (hr : 0 < r) (x : LoopPlane) :
    HasDerivAt (fun s => averagingValue u s x)
      (-(∫ z, averagingKernel r (x - z) *
        ∑ i : Fin 2, ((x i - z i) / r) * d i z)) r := by
  let φ := averagingRadiusTest hr x
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  have hu := (Lp.memLp u).locallyIntegrable (by norm_num)
  apply (averagingValue_radius_hasDerivAt hu hr x).congr_deriv
  change (∫ z, u z * ∑ i : Fin 2, fderiv ℝ (φ i) z (b i)) = _
  have hi (i : Fin 2) : Integrable (fun z => u z * fderiv ℝ (φ i) z (b i)) := by
    exact (Lp.memLp u).integrable_mul ((∂_{b i} (φ i)).memLp 2 volume)
  have hj (i : Fin 2) : Integrable (fun z => d i z * φ i z) :=
    (Lp.memLp (d i)).integrable_mul ((φ i).memLp 2 volume)
  have heq (i : Fin 2) :
      (∫ z, u z * fderiv ℝ (φ i) z (b i)) = -(∫ z, d i z * φ i z) := by
    have h := hw i (φ i)
    rw [DeTurckDomainRegularityNative.inner_schwartz] at h
    dsimp only [b]
    linarith only [h]
  simp only [Fin.sum_univ_two, mul_add]
  rw [integral_add (hi 0) (hi 1), heq 0, heq 1, ← neg_add, ← integral_add (hj 0) (hj 1)]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  change d 0 z * (((x 0 - z 0) / r) * averagingKernel r (x - z)) +
    d 1 z * (((x 1 - z 1) / r) * averagingKernel r (x - z)) = _
  ring

end PoincareConjecture.M65Interior
