import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.DiskGreen
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerRescaling











set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Pointwise

namespace PoincareConjecture

open Proofs.M58



theorem m64Affine_image_unitDisk (a : LoopPlane) {r : ℝ} (hr : 0 < r) :
    (fun z : LoopPlane => a + r • z) '' loopDiskSet = Metric.closedBall a r := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hr.le]
    exact mul_le_of_le_one_right hr.le (mem_closedBall_zero_iff.mp hw)
  · intro hz
    refine ⟨r⁻¹ • (z - a), ?_, ?_⟩
    · rw [loopDiskSet, mem_closedBall_zero_iff, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
      have hh := mul_le_mul_of_nonneg_left
        (show ‖z - a‖ ≤ r from by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz)
        (inv_nonneg.mpr hr.le)
      simpa only [inv_mul_cancel₀ hr.ne'] using hh
    · change a + r • (r⁻¹ • (z - a)) = z
      rw [smul_inv_smul₀ hr.ne']
      abel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in


theorem m64Affine_integral_vector (F : LoopPlane → E) (a : LoopPlane)
    {r : ℝ} (hr : 0 < r) (S : Set LoopPlane) :
    (∫ z in S, r ^ 2 • F (a + r • z)) =
      ∫ z in (fun w => a + r • w) '' S, F z := by
  rw [integral_smul,
    Measure.setIntegral_comp_smul_of_pos volume (fun w => F (a + w)) S hr]
  have hdim : Module.finrank ℝ LoopPlane = 2 := by simp [LoopPlane]
  rw [hdim, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hr.ne'), one_smul]
  have ht := (measurePreserving_add_left (volume : Measure LoopPlane) a).setIntegral_image_emb
    (MeasurableEquiv.addLeft a).measurableEmbedding F (r • S)
  have hset : (fun x : LoopPlane => a + x) '' (r • S) =
      (fun w => a + r • w) '' S := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨v, hv, rfl⟩ := hw
      exact ⟨v, hv, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨r • w, ⟨w, hw, rfl⟩, rfl⟩
  rw [← ht, hset]



theorem m64Disk_integral_partial_rescaled {f : LoopPlane → E} (hf : ContDiff ℝ 1 f)
    (a : LoopPlane) {r : ℝ} (hr : 0 < r) (i : Fin 2) :
    (∫ z in Metric.closedBall a r, fderiv ℝ f z (EuclideanSpace.single i 1)) =
      r • ∫ t in Icc (-Real.pi) Real.pi,
        angularPoint t i • f (a + r • angularPoint t) := by
  let A := fun z : LoopPlane => a + r • z
  let D := fun z => fderiv ℝ f z (EuclideanSpace.single i 1)
  have hA : ContDiff ℝ 1 A := by
    simpa +instances only [A, id_eq] using!
      contDiff_const.add ((contDiff_id : ContDiff ℝ 1 (fun z : LoopPlane => z)).const_smul r)
  have hAD (z : LoopPlane) : HasFDerivAt A (r • ContinuousLinearMap.id ℝ LoopPlane) z := by
    simpa +instances only [zero_add, id_eq] using!
      (hasFDerivAt_const a z).add ((hasFDerivAt_id z).const_smul r)
  have hD (z : LoopPlane) : fderiv ℝ (f ∘ A) z (EuclideanSpace.single i 1) = r • D (A z) := by
    rw [fderiv_comp z (hf.differentiable (by simp) (A z))
      (hA.differentiable (by simp) z), (hAD z).fderiv]
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul, D]
  have hscaled := m64Affine_integral_vector D a hr loopDiskSet
  rw [m64Affine_image_unitDisk a hr] at hscaled
  calc
    _ = ∫ z in loopDiskSet, r ^ 2 • D (A z) := hscaled.symm
    _ = r • ∫ z in loopDiskSet, fderiv ℝ (f ∘ A) z (EuclideanSpace.single i 1) := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hD, smul_smul, pow_two]
    _ = _ := by rw [m64Disk_integral_partial (hf.comp hA) i]; rfl



theorem m64Disk_green_identity_rescaled {f : LoopPlane → E} {phi : LoopPlane → ℝ}
    (hf : ContDiff ℝ 1 f) (hphi : ContDiff ℝ 1 phi)
    (a : LoopPlane) {r : ℝ} (hr : 0 < r) (i : Fin 2) :
    (∫ z in Metric.closedBall a r, phi z • fderiv ℝ f z (EuclideanSpace.single i 1)) +
      (∫ z in Metric.closedBall a r, fderiv ℝ phi z (EuclideanSpace.single i 1) • f z) =
        r • ∫ t in Icc (-Real.pi) Real.pi,
          angularPoint t i • (phi (a + r • angularPoint t) • f (a + r • angularPoint t)) := by
  let v : LoopPlane := EuclideanSpace.single i 1
  have hleft : IntegrableOn (fun z => phi z • fderiv ℝ f z v) (Metric.closedBall a r) volume :=
    (hphi.continuous.smul ((hf.continuous_fderiv (by simp)).clm_apply continuous_const))
      |>.continuousOn.integrableOn_compact (isCompact_closedBall a r)
  have hright : IntegrableOn (fun z => fderiv ℝ phi z v • f z) (Metric.closedBall a r) volume :=
    (((hphi.continuous_fderiv (by simp)).clm_apply continuous_const).smul hf.continuous)
      |>.continuousOn.integrableOn_compact (isCompact_closedBall a r)
  have hprod (z : LoopPlane) :
      fderiv ℝ (fun p => phi p • f p) z v =
        phi z • fderiv ℝ f z v + fderiv ℝ phi z v • f z := by
    rw [fderiv_fun_smul (hphi.differentiable (by simp) z) (hf.differentiable (by simp) z),
      add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [← integral_add hleft hright]
  calc
    _ = ∫ z in Metric.closedBall a r, fderiv ℝ (fun p => phi p • f p) z v :=
      integral_congr_ae (Eventually.of_forall (fun z => (hprod z).symm))
    _ = _ := m64Disk_integral_partial_rescaled (hphi.smul hf) a hr i

end PoincareConjecture
