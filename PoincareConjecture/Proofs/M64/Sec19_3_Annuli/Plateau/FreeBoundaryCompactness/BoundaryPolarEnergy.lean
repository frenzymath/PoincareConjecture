import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.BoundaryPolarStrip
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PolarPullback









set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M64

open Proofs.M58

local notation "S" => interior m64AnnulusDomain
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)




theorem boundaryPolarStrip_weighted_integral
    (x : ℝ) {rho : ℝ} (hrho : 0 < rho) {F : LoopPlane → ℝ}
    (hF : IntegrableOn F (upperBoundaryShell x rho)) (hpos : ∀ p, 0 ≤ F p) :
    IntegrableOn (fun p => (rho * Real.exp (-p 1)) ^ 2 / 2 *
      F (boundaryPolarStrip x rho p)) S ∧
    (∫ p in S, (rho * Real.exp (-p 1)) ^ 2 / 2 * F (boundaryPolarStrip x rho p)) ≤
      ∫ p in upperBoundaryShell x rho, F p := by
  have hmap := (boundaryPolarStrip_mapsTo_shell x hrho).image_subset
  have hw := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    isOpen_interior.measurableSet
    (fun p _ => ((boundaryPolarStrip_contDiff x rho).differentiable (by simp) p)
      |>.hasFDerivAt.hasFDerivWithinAt) (boundaryPolarStrip_injOn x hrho) F).mp
        (hF.mono_set hmap)
  have hdet (p : LoopPlane) : |(fderiv ℝ (boundaryPolarStrip x rho) p).det| =
      (rho * Real.exp (-p 1)) ^ 2 / 2 := by
    rw [boundaryPolarStrip_det, abs_of_nonneg (by positivity)]
  refine ⟨by simpa only [hdet, smul_eq_mul] using hw, ?_⟩
  calc
    _ = ∫ p in boundaryPolarStrip x rho '' S, F p := by
      simpa only [hdet, smul_eq_mul] using
        (integral_image_eq_integral_abs_det_fderiv_smul volume
          isOpen_interior.measurableSet
          (fun p _ => ((boundaryPolarStrip_contDiff x rho).differentiable (by simp) p)
            |>.hasFDerivAt.hasFDerivWithinAt) (boundaryPolarStrip_injOn x hrho) F).symm
    _ ≤ _ := setIntegral_mono_set hF (Eventually.of_forall hpos) (Eventually.of_forall hmap)



def phaseGradientDensity (L : LoopPlane → ℝ) (p : LoopPlane) : ℝ :=
  (fderiv ℝ L p e0) ^ 2 + (fderiv ℝ L p e1) ^ 2



def boundaryAngularDerivative (L : LoopPlane → ℝ) (x rho : ℝ) (p : LoopPlane) : ℝ :=
  fderiv ℝ L (boundaryPolarStrip x rho p)
    ((rho * Real.exp (-p 1) / 2) • angularVector (p 0 / 2))



theorem boundaryAngularDerivative_sq_le (L : LoopPlane → ℝ) (x rho : ℝ) (p : LoopPlane) :
    boundaryAngularDerivative L x rho p ^ 2 ≤
      (1 / 2 : ℝ) * ((rho * Real.exp (-p 1)) ^ 2 / 2 *
        phaseGradientDensity L (boundaryPolarStrip x rho p)) := by
  let a := fderiv ℝ L (boundaryPolarStrip x rho p) e0
  let b := fderiv ℝ L (boundaryPolarStrip x rho p) e1
  let theta := p 0 / 2
  have hang : angularVector theta = (-Real.sin theta) • e0 + Real.cos theta • e1 := by
    ext i
    fin_cases i <;> simp [angularVector]
  have hscalar : (-Real.sin theta * a + Real.cos theta * b) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    have htrig := congrArg (fun z : ℝ => (a ^ 2 + b ^ 2) * z)
      (Real.sin_sq_add_cos_sq theta)
    nlinarith [sq_nonneg (Real.cos theta * a + Real.sin theta * b)]
  have h := mul_le_mul_of_nonneg_left hscalar
    (sq_nonneg (rho * Real.exp (-p 1) / 2))
  unfold boundaryAngularDerivative
  change (fderiv ℝ L (boundaryPolarStrip x rho p)
    ((rho * Real.exp (-p 1) / 2) • angularVector theta)) ^ 2 ≤ _
  rw [hang, map_smul, map_add, map_smul, map_smul]
  change ((rho * Real.exp (-p 1) / 2) *
    (-Real.sin theta * a + Real.cos theta * b)) ^ 2 ≤ _
  dsimp only [phaseGradientDensity]
  change _ ≤ (1 / 2 : ℝ) * ((rho * Real.exp (-p 1)) ^ 2 / 2 * (a ^ 2 + b ^ 2))
  nlinarith [h]




theorem boundaryAngularDerivative_shell_energy
    (L : LoopPlane → ℝ) (hL : ContDiffOn ℝ 1 L S)
    {x rho : ℝ} (hrho : 0 < rho) (hx : rho < x)
    (hP : x + rho < curvePeriod) (hr : rho < 1)
    (hF : IntegrableOn (phaseGradientDensity L) (upperBoundaryShell x rho)) :
    IntegrableOn (fun p => boundaryAngularDerivative L x rho p ^ 2) S ∧
      (∫ p in S, boundaryAngularDerivative L x rho p ^ 2) ≤
        (1 / 2 : ℝ) * ∫ p in upperBoundaryShell x rho, phaseGradientDensity L p := by
  have hmap : MapsTo (boundaryPolarStrip x rho) S S :=
    fun p hp => upperBoundaryShell_subset_interior hx hP hr
      (boundaryPolarStrip_mapsTo_shell x hrho hp)
  have hDf : ContinuousOn (fderiv ℝ L) S :=
    (hL.fderiv_of_isOpen isOpen_interior (m := 0) (by norm_num)).continuousOn
  have hfield : Continuous (fun p : LoopPlane =>
      (rho * Real.exp (-p 1) / 2) • angularVector (p 0 / 2)) := by
    unfold angularVector
    fun_prop
  have hD : ContinuousOn (boundaryAngularDerivative L x rho) S :=
    (hDf.comp (boundaryPolarStrip_contDiff x rho).continuous.continuousOn hmap).clm_apply
      hfield.continuousOn
  obtain ⟨hweighted, hle⟩ := boundaryPolarStrip_weighted_integral x hrho hF
    (fun p => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hint : IntegrableOn (fun p => boundaryAngularDerivative L x rho p ^ 2) S := by
    apply (hweighted.const_mul (1 / 2 : ℝ)).mono'
      ((hD.pow 2).aestronglyMeasurable isOpen_interior.measurableSet)
    filter_upwards with p
    change ‖boundaryAngularDerivative L x rho p ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact boundaryAngularDerivative_sq_le L x rho p
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ p in S, (1 / 2 : ℝ) * ((rho * Real.exp (-p 1)) ^ 2 / 2 *
        phaseGradientDensity L (boundaryPolarStrip x rho p)) :=
      integral_mono hint (hweighted.const_mul _) (boundaryAngularDerivative_sq_le L x rho)
    _ = (1 / 2 : ℝ) * ∫ p in S, (rho * Real.exp (-p 1)) ^ 2 / 2 *
        phaseGradientDensity L (boundaryPolarStrip x rho p) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hle (by norm_num)

end PoincareConjecture.M64
