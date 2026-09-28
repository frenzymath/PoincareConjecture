import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.DiskDivergence
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityPolarMeasure
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology ContDiff Pointwise SchwartzMap InnerProductSpace

namespace PoincareConjecture.M65Interior

theorem integral_disk_affine (f : LoopPlane → ℝ) (x : LoopPlane) {R : ℝ} (hR : 0 < R) :
    (∫ z in loopDiskSet, f (x + R • z)) =
      (R ^ 2)⁻¹ * ∫ z in closedBall x R, f z := by
  have hscale := Measure.setIntegral_comp_smul_of_pos volume
    (fun z => f (x + z)) loopDiskSet hR
  have hball : R • loopDiskSet = closedBall (0 : LoopPlane) R := by
    rw [loopDiskSet, smul_closedBall' hR.ne']
    simp only [smul_zero, Real.norm_eq_abs, abs_of_pos hR, mul_one]
  have htrans := (measurePreserving_add_left volume x).setIntegral_preimage_emb
    (Homeomorph.addLeft x).measurableEmbedding f (closedBall x R)
  have hpre : (fun z : LoopPlane => x + z) ⁻¹' closedBall x R = closedBall 0 R := by
    ext z
    simp only [mem_preimage, mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero]
  rw [hpre] at htrans
  simpa only [finrank_euclideanSpace, Fintype.card_fin, hball, smul_eq_mul, htrans] using hscale

theorem integral_divergence_disk (X : LoopPlane → LoopPlane) (hX : ContDiff ℝ 1 X)
    (x : LoopPlane) {R : ℝ} (hR : 0 < R) :
    (∫ z in closedBall x R, ∑ i : Fin 2,
      inner ℝ (fderiv ℝ X z (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
      R * ∫ θ in (-Real.pi)..Real.pi,
        inner ℝ (X (polarPlane x (R, θ))) (Proofs.M58.angularPoint θ) := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let Y (z : LoopPlane) := X (x + R • z)
  let D (z : LoopPlane) := ∑ i : Fin 2, inner ℝ (fderiv ℝ X z (b i)) (b i)
  have hY : ContDiff ℝ 1 Y := hX.comp (contDiff_const.add (contDiff_id.const_smul R))
  have hdiv (z : LoopPlane) :
      (∑ i : Fin 2, inner ℝ (fderiv ℝ Y z (b i)) (b i)) = R * D (x + R • z) := by
    have hd := ((hX.differentiable one_ne_zero) (x + R • z)).hasFDerivAt.comp z
      ((hasFDerivAt_const x z).add ((hasFDerivAt_id z).const_smul R))
    change HasFDerivAt (fun y => X (x + R • y)) _ z at hd
    change (∑ i : Fin 2, inner ℝ (fderiv ℝ (fun z => X (x + R • z)) z (b i))
      (b i)) = _
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
      zero_add, map_smul, real_inner_smul_left, Finset.mul_sum, D]
  have hunit := m65Integral_divergence_loopDisk Y (fun _ _ => hY.contDiffAt)
  change (∫ z in loopDiskSet, ∑ i : Fin 2,
    inner ℝ (fderiv ℝ Y z (b i)) (b i)) = _ at hunit
  simp_rw [hdiv] at hunit
  rw [integral_const_mul, integral_disk_affine D x hR] at hunit
  change (∫ z in closedBall x R, D z) = _
  calc
    _ = R * (R * ((R ^ 2)⁻¹ * ∫ z in closedBall x R, D z)) := by
      field_simp
    _ = _ := by rw [hunit]; rfl

theorem smooth_disk_green (f : LoopPlane → ℝ) (hf : ContDiff ℝ 1 f)
    (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) (x : LoopPlane) {R : ℝ} (hR : 0 < R) :
    (∫ z in closedBall x R,
      fderiv ℝ f z (EuclideanSpace.basisFun (Fin 2) ℝ i) * test z +
        f z * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
      R * ∫ θ in (-Real.pi)..Real.pi,
        f (polarPlane x (R, θ)) * test (polarPlane x (R, θ)) *
          Proofs.M58.angularPoint θ i := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let X (z : LoopPlane) := (f z * test z) • b i
  have hX : ContDiff ℝ 1 X := (hf.mul (test.smooth 1)).smul contDiff_const
  have hdiv (z : LoopPlane) :
      (∑ j : Fin 2, inner ℝ (fderiv ℝ X z (b j)) (b j)) =
        fderiv ℝ f z (b i) * test z + f z * fderiv ℝ test z (b i) := by
    have hd := ((hf.differentiable one_ne_zero z).hasFDerivAt.mul
      (test.differentiableAt (x := z)).hasFDerivAt).smul_const (b i)
    change HasFDerivAt (fun y => (f y * test y) • b i) _ z at hd
    change (∑ j : Fin 2, inner ℝ (fderiv ℝ (fun z => (f z * test z) • b i) z
      (b j)) (b j)) = _
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.smulRight_apply, real_inner_smul_left]
    rw [Finset.sum_eq_single i]
    · simp only [b.inner_eq_one, mul_one, add_apply, smul_apply, smul_eq_mul]
      ring
    · intro j _ hji
      rw [b.inner_eq_zero hji.symm, mul_zero]
    · simp
  calc
    _ = ∫ z in closedBall x R, ∑ j : Fin 2,
        inner ℝ (fderiv ℝ X z (b j)) (b j) := by
      apply setIntegral_congr_fun isClosed_closedBall.measurableSet
      intro z _
      exact (hdiv z).symm
    _ = R * ∫ θ in (-Real.pi)..Real.pi,
        inner ℝ (X (polarPlane x (R, θ))) (Proofs.M58.angularPoint θ) :=
      integral_divergence_disk X hX x hR
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [X, real_inner_smul_left, b, EuclideanSpace.basisFun_inner]

end PoincareConjecture.M65Interior
