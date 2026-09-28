import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTraceEstimate
import Mathlib.Analysis.Normed.Module.Dual












set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]



theorem m64AnnulusInteriorIntegral_eq_iterated_vector (f : LoopPlane → F)
    (hf : Continuous f) :
    (∫ p in interior m64AnnulusDomain, f p) =
      ∫ x in Icc (0 : ℝ) curvePeriod, ∫ s in Icc (0 : ℝ) 1, f (annulusPoint x s) := by
  have hfi : IntegrableOn f (interior m64AnnulusDomain) volume :=
    hf.continuousOn.integrableOn_compact m64AnnulusDomain_isCompact
      |>.mono_set interior_subset
  have hc : Continuous (fun q : ℝ × ℝ => f (annulusPoint q.1 q.2)) := by
    apply hf.comp
    unfold annulusPoint
    fun_prop
  have hInt : Integrable (fun q : ℝ × ℝ => f (annulusPoint q.1 q.2))
      ((volume.restrict (Icc (0 : ℝ) curvePeriod)).prod
        (volume.restrict (Icc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hs (x : ℝ) : IntegrableOn (fun s => f (annulusPoint x s)) (Icc (0 : ℝ) 1) volume := by
    have hh : Continuous (fun s => f (annulusPoint x s)) := by
      apply hf.comp
      unfold annulusPoint
      fun_prop
    exact hh.integrableOn_Icc
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro L
  rw [← L.integral_comp_comm hfi, ← L.integral_comp_comm hInt.integral_prod_left]
  simp_rw [← L.integral_comp_comm (hs _)]
  exact m64AnnulusInteriorIntegral_eq_iterated (fun p => L (f p)) (L.continuous.comp hf)



theorem m64Annulus_integral_vertical_derivative
    {f : LoopPlane → F} (hf : ContDiff ℝ 1 f) :
    (∫ p in interior m64AnnulusDomain,
      fderiv ℝ f p (EuclideanSpace.single (1 : Fin 2) 1)) =
      ∫ x in Icc (0 : ℝ) curvePeriod, f (annulusPoint x 1) - f (annulusPoint x 0) := by
  let D : LoopPlane → F := fun p => fderiv ℝ f p (EuclideanSpace.single (1 : Fin 2) 1)
  have hD : Continuous D := (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  rw [m64AnnulusInteriorIntegral_eq_iterated_vector D hD]
  apply integral_congr_ae
  filter_upwards [] with x
  have hd : Continuous (fun s => D (annulusPoint x s)) := by
    apply hD.comp
    unfold annulusPoint
    fun_prop
  have hder (s : ℝ) : HasDerivAt (fun t => f (annulusPoint x t))
      (D (annulusPoint x s)) s :=
    (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s
      (m64AnnulusPoint_vertical_hasDerivAt x s)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hder s)
    (hd.intervalIntegrable 0 1)



theorem m64Annulus_vertical_green_identity
    {f : LoopPlane → F} {phi : LoopPlane → ℝ}
    (hf : ContDiff ℝ 1 f) (hphi : ContDiff ℝ 1 phi) :
    (∫ p in interior m64AnnulusDomain,
      phi p • fderiv ℝ f p (EuclideanSpace.single (1 : Fin 2) 1)) +
      (∫ p in interior m64AnnulusDomain,
        fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1) • f p) =
      ∫ x in Icc (0 : ℝ) curvePeriod,
        phi (annulusPoint x 1) • f (annulusPoint x 1) -
          phi (annulusPoint x 0) • f (annulusPoint x 0) := by
  let v : LoopPlane := EuclideanSpace.single (1 : Fin 2) 1
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
    _ = _ := m64Annulus_integral_vertical_derivative (hphi.smul hf)

end PoincareConjecture
