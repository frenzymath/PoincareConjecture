import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetDiskStokes
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityDiskGreen











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture.M65Gauss





theorem integral_divergence_disk_off_countable
    (X : LoopPlane → LoopPlane) (d : LoopPlane → ℝ) (S : Set LoopPlane)
    (hS : S.Countable) (x : LoopPlane) {R : ℝ} (hR : 0 < R)
    (hX : ContinuousOn X (closedBall x R))
    (hXi : ∀ z ∈ ball x R \ S, ContDiffAt ℝ 1 X z)
    (hd : IntegrableOn d (closedBall x R))
    (hdiv : ∀ z ∈ ball x R \ S,
      (∑ i : Fin 2, inner ℝ ((fderiv ℝ X z) (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) = d z) :
    (∫ z in closedBall x R, d z) =
      R * ∫ θ in (-Real.pi)..Real.pi,
        inner ℝ (X (x + R • Proofs.M58.angularPoint θ))
          (Proofs.M58.angularPoint θ) := by
  let A : LoopPlane → LoopPlane := fun z => x + R • z
  let Y : LoopPlane → LoopPlane := X ∘ A
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  have hA : ContDiff ℝ 1 A := contDiff_const.add (contDiff_id.const_smul R)
  have hAinj : Function.Injective A := fun z w h =>
    (smul_right_injective _ hR.ne') (add_left_cancel h)
  have hAc (z : LoopPlane) (hz : z ∈ loopDiskSet) : A z ∈ closedBall x R := by
    rw [mem_closedBall, dist_eq_norm]
    simp only [A, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    have hh : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    nlinarith
  have hAi (z : LoopPlane) (hz : z ∈ ball (0 : LoopPlane) 1) : A z ∈ ball x R := by
    rw [mem_ball, dist_eq_norm]
    simp only [A, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    have hh : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    nlinarith
  have hYC : ContinuousOn Y loopDiskSet :=
    hX.comp hA.continuous.continuousOn hAc
  have hYI (z : LoopPlane) (hz : z ∈ ball (0 : LoopPlane) 1 \ A ⁻¹' S) :
      ContDiffAt ℝ 1 Y z := (hXi _ ⟨hAi z hz.1, hz.2⟩).comp z hA.contDiffAt
  let d0 := (closedBall x R).indicator d
  have hd0 : Integrable d0 := hd.integrable_indicator measurableSet_closedBall
  have hdt : Integrable (fun z : LoopPlane => d0 (x + z)) :=
    (measurePreserving_add_left volume x).integrable_comp_of_integrable (g := d0) hd0
  have hdA : IntegrableOn (fun z => d (A z)) loopDiskSet := by
    apply (hdt.comp_smul hR.ne').integrableOn.congr_fun _ measurableSet_closedBall
    intro z hz
    exact indicator_of_mem (hAc z hz) d
  have hDY (z : LoopPlane) (hz : z ∈ ball (0 : LoopPlane) 1 \ A ⁻¹' S) :
      (∑ i : Fin 2, inner ℝ (fderiv ℝ Y z (b i)) (b i)) = R * d (A z) := by
    have h := ((hXi _ ⟨hAi z hz.1, hz.2⟩).differentiableAt (by simp)).hasFDerivAt.comp z
      ((hasFDerivAt_const x z).add ((hasFDerivAt_id z).const_smul R))
    change HasFDerivAt Y _ z at h
    rw [h.fderiv]
    simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
      zero_add, map_smul, real_inner_smul_left, ← Finset.mul_sum]
    rw [hdiv _ ⟨hAi z hz.1, hz.2⟩]
  have hunit := integral_divergence_loopDisk_off_countable Y
    (fun z => R * d (A z)) (A ⁻¹' S) (hS.preimage hAinj) hYC hYI
    (hdA.const_mul R) hDY
  rw [integral_const_mul, M65Interior.integral_disk_affine d x hR] at hunit
  calc
    _ = R * (R * ((R ^ 2)⁻¹ * ∫ z in closedBall x R, d z)) := by
      field_simp
    _ = _ := by rw [hunit]; rfl

end PoincareConjecture.M65Gauss
