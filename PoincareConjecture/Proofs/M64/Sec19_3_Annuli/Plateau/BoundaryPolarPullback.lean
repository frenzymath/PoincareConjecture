import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.BoundaryPolarEnergy










noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture.M64

local notation "S" => interior m64AnnulusDomain




theorem boundaryPolarStrip_integrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : ℝ) {rho : ℝ} (hrho : 0 < rho) {F : LoopPlane → E}
    (hF : IntegrableOn F (upperBoundaryShell x rho)) :
    IntegrableOn (fun p => F (boundaryPolarStrip x rho p)) S := by
  let P := boundaryPolarStrip x rho
  let J := fun p : LoopPlane => (rho * Real.exp (-p 1)) ^ 2 / 2
  let c := (rho * Real.exp (-1)) ^ 2 / 2
  have hc : 0 < c := by dsimp only [c]; positivity
  have hw := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    isOpen_interior.measurableSet
    (fun p _ => ((boundaryPolarStrip_contDiff x rho).differentiable (by simp) p)
      |>.hasFDerivAt.hasFDerivWithinAt) (boundaryPolarStrip_injOn x hrho) F).mp
    (hF.mono_set (boundaryPolarStrip_mapsTo_shell x hrho).image_subset)
  have hdet (p : LoopPlane) : |(fderiv ℝ P p).det| = J p := by
    rw [boundaryPolarStrip_det, abs_of_nonneg (by positivity)]
  have hw' : IntegrableOn (fun p => J p • F (P p)) S := by
    change IntegrableOn (fun p => |(fderiv ℝ P p).det| • F (P p)) S at hw
    simpa only [hdet] using hw
  have hJ : Continuous (fun p => (J p)⁻¹) := by
    apply Continuous.inv₀
    · dsimp only [J]; fun_prop
    · intro p; dsimp only [J]; positivity
  have hb : ∀ᵐ p ∂volume.restrict S, ‖(J p)⁻¹‖ ≤ c⁻¹ := by
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
    have hs := (m64AnnulusInterior_coordinates p).mp hp
    have hr : rho * Real.exp (-1) ≤ rho * Real.exp (-p 1) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hs.2.2.2])) hrho.le
    have hj : c ≤ J p := div_le_div_of_nonneg_right
      ((sq_le_sq₀ (by positivity) (by positivity)).mpr hr) (by norm_num)
    rw [Real.norm_eq_abs, abs_of_pos (by dsimp only [J]; positivity)]
    exact inv_anti₀ hc hj
  have hi := hw'.bdd_smul c⁻¹ hJ.aestronglyMeasurable hb
  have heq : (fun p => (J p)⁻¹ • (J p • F (P p))) = (fun p => F (P p)) := by
    funext p
    rw [smul_smul, inv_mul_cancel₀ (by dsimp only [J]; positivity), one_smul]
  change IntegrableOn (fun p => (J p)⁻¹ • (J p • F (P p))) S at hi
  rwa [heq] at hi




theorem boundaryPolarStrip_memLp_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : ℝ) {rho : ℝ} (hrho : 0 < rho) {F : LoopPlane → E}
    (hF : MemLp F 2 (volume.restrict (upperBoundaryShell x rho))) :
    MemLp (fun p => F (boundaryPolarStrip x rho p)) 2 (volume.restrict S) := by
  let : IsFiniteMeasure (volume.restrict (upperBoundaryShell x rho)) :=
    isFiniteMeasure_restrict.mpr (ne_top_of_le_ne_top
      (isCompact_closedBall (annulusPoint x 0) rho).measure_lt_top.ne
      (measure_mono (fun _ hp => hp.1.1)))
  have hi := boundaryPolarStrip_integrable x hrho (hF.integrable (by norm_num))
  apply (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mpr
  exact boundaryPolarStrip_integrable x hrho hF.norm.integrable_sq




theorem boundaryPolarStrip_ae (x : ℝ) {rho : ℝ} (hrho : 0 < rho)
    {q : LoopPlane → Prop} (hq : ∀ᵐ p ∂volume.restrict (upperBoundaryShell x rho), q p) :
    ∀ᵐ p ∂volume.restrict S, q (boundaryPolarStrip x rho p) := by
  classical
  let F := fun p : LoopPlane => if q p then (0 : ℝ) else 1
  have hz : F =ᵐ[volume.restrict (upperBoundaryShell x rho)] (fun _ => (0 : ℝ)) :=
    hq.mono (fun p hp => by simp [F, hp])
  have hi : IntegrableOn F (upperBoundaryShell x rho) := (integrable_zero _ _ _).congr hz.symm
  have hpos (p : LoopPlane) : 0 ≤ F p := by dsimp only [F]; split_ifs <;> norm_num
  obtain ⟨hwi, hle⟩ := boundaryPolarStrip_weighted_integral x hrho hi hpos
  have hzero : (∫ p in upperBoundaryShell x rho, F p) = 0 := by
    simpa only [integral_zero] using integral_congr_ae hz
  rw [hzero] at hle
  have heq := le_antisymm hle (integral_nonneg (fun p => mul_nonneg (by positivity) (hpos _)))
  have hgood := (integral_eq_zero_iff_of_nonneg
    (fun p => mul_nonneg (by positivity) (hpos _)) hwi).mp heq
  filter_upwards [hgood] with p hp
  by_contra hnot
  have hj : 0 < (rho * Real.exp (-p 1)) ^ 2 / 2 := by positivity
  simp only [F, if_neg hnot, mul_one, Pi.zero_apply] at hp
  exact hj.ne' hp

end PoincareConjecture.M64
