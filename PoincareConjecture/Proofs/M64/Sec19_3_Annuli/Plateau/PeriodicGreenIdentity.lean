import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RectangleGreenIdentity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CirclePhaseEnergy












set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]



theorem m64Annulus_integral_horizontal_derivative
    {f : LoopPlane → F} (hf : ContDiff ℝ 1 f) :
    (∫ p in interior m64AnnulusDomain,
      fderiv ℝ f p (EuclideanSpace.single (0 : Fin 2) 1)) =
      ∫ s in Icc (0 : ℝ) 1,
        f (annulusPoint curvePeriod s) - f (annulusPoint 0 s) := by
  let D : LoopPlane → F := fun p => fderiv ℝ f p (EuclideanSpace.single (0 : Fin 2) 1)
  have hD : Continuous D := (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hprod : Continuous (fun q : ℝ × ℝ => D (annulusPoint q.1 q.2)) := by
    apply hD.comp
    unfold annulusPoint
    fun_prop
  have hInt : Integrable (fun q : ℝ × ℝ => D (annulusPoint q.1 q.2))
      ((volume.restrict (Icc (0 : ℝ) curvePeriod)).prod
        (volume.restrict (Icc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact hprod.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [m64AnnulusInteriorIntegral_eq_iterated_vector D hD, integral_integral_swap hInt]
  apply integral_congr_ae
  filter_upwards [] with s
  have hd : Continuous (fun x => D (annulusPoint x s)) := by
    apply hD.comp
    unfold annulusPoint
    fun_prop
  have hder (x : ℝ) : HasDerivAt (fun y => f (annulusPoint y s))
      (D (annulusPoint x s)) x :=
    (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt x
      (m64AnnulusPoint_horizontal_hasDerivAt s x)
  have hp : 0 ≤ curvePeriod := by unfold curvePeriod; positivity
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hp]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hder x)
    (hd.intervalIntegrable 0 curvePeriod)



theorem m64Annulus_horizontal_green_identity
    {f : LoopPlane → F} {phi : LoopPlane → ℝ}
    (hf : ContDiff ℝ 1 f) (hphi : ContDiff ℝ 1 phi) :
    (∫ p in interior m64AnnulusDomain,
      phi p • fderiv ℝ f p (EuclideanSpace.single (0 : Fin 2) 1)) +
      (∫ p in interior m64AnnulusDomain,
        fderiv ℝ phi p (EuclideanSpace.single (0 : Fin 2) 1) • f p) =
      ∫ s in Icc (0 : ℝ) 1,
        phi (annulusPoint curvePeriod s) • f (annulusPoint curvePeriod s) -
          phi (annulusPoint 0 s) • f (annulusPoint 0 s) := by
  let v : LoopPlane := EuclideanSpace.single (0 : Fin 2) 1
  have hdf : Continuous (fun p => fderiv ℝ f p v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdp : Continuous (fun p => fderiv ℝ phi p v) :=
    (hphi.continuous_fderiv (by simp)).clm_apply continuous_const
  have hleft : IntegrableOn (fun p => phi p • fderiv ℝ f p v)
      (interior m64AnnulusDomain) volume :=
    (hphi.continuous.smul hdf).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact |>.mono_set interior_subset
  have hright : IntegrableOn (fun p => fderiv ℝ phi p v • f p)
      (interior m64AnnulusDomain) volume :=
    (hdp.smul hf.continuous).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact |>.mono_set interior_subset
  rw [← integral_add hleft hright]
  have hprod (p : LoopPlane) :
      fderiv ℝ (fun q => phi q • f q) p v =
        phi p • fderiv ℝ f p v + fderiv ℝ phi p v • f p := by
    rw [fderiv_fun_smul (hphi.differentiable (by simp) p)
      (hf.differentiable (by simp) p), add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
  calc
    _ = ∫ p in interior m64AnnulusDomain, fderiv ℝ (fun q => phi q • f q) p v :=
      integral_congr_ae (Filter.Eventually.of_forall fun p => (hprod p).symm)
    _ = _ := m64Annulus_integral_horizontal_derivative (hphi.smul hf)



theorem m64Annulus_periodic_green_identity
    {f : LoopPlane → F} {phi : LoopPlane → ℝ}
    (hf : ContDiff ℝ 1 f) (hphi : ContDiff ℝ 1 phi)
    (hperiodic : ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (hphi_seam : ∀ s ∈ Icc (0 : ℝ) 1,
      phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) :
    (∫ p in interior m64AnnulusDomain,
      phi p • fderiv ℝ f p (EuclideanSpace.single (0 : Fin 2) 1)) +
      (∫ p in interior m64AnnulusDomain,
        fderiv ℝ phi p (EuclideanSpace.single (0 : Fin 2) 1) • f p) = 0 := by
  rw [m64Annulus_horizontal_green_identity hf hphi]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have hseam : f (annulusPoint curvePeriod s) = f (annulusPoint 0 s) := by
    simpa only [zero_add] using hperiodic 0 s
  rw [hseam, hphi_seam s hs, sub_self]
  rfl

end PoincareConjecture
