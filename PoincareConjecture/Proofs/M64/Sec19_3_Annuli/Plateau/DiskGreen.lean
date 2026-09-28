import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.DiskGreenGeometry
import PoincareConjecture.Proofs.M58.Cor18_28_PolarIntegration
import Mathlib.Analysis.Normed.Module.Dual

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

open Proofs.M58

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem m64Integral_loopDisk_polar_vector (f : LoopPlane → E) (hf : Continuous f) :
    (∫ z in loopDiskSet, f z) =
      ∫ p in Ioc (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • f (p.1 • angularPoint p.2) := by
  have hd : IntegrableOn f loopDiskSet volume :=
    hf.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)
  have hc : Continuous (fun p : ℝ × ℝ => p.1 • f (p.1 • angularPoint p.2)) :=
    continuous_fst.smul (hf.comp (continuous_fst.smul
      (contDiff_angularPoint.continuous.comp continuous_snd)))
  have hp : IntegrableOn (fun p : ℝ × ℝ => p.1 • f (p.1 • angularPoint p.2))
      (Ioc (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi) volume :=
    hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      |>.mono_set (prod_mono Ioc_subset_Icc_self Ioo_subset_Icc_self)
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro L
  calc
    _ = ∫ z in loopDiskSet, L (f z) := (L.integral_comp_comm hd).symm
    _ = ∫ p in Ioc (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 * L (f (p.1 • angularPoint p.2)) := integral_loopDisk_polar _
    _ = _ := by simpa only [map_smul, smul_eq_mul] using L.integral_comp_comm hp

theorem m64Disk_integral_partial {f : LoopPlane → E} (hf : ContDiff ℝ 1 f) (i : Fin 2) :
    (∫ z in loopDiskSet, fderiv ℝ f z (EuclideanSpace.single i 1)) =
      ∫ t in Icc (-Real.pi) Real.pi, angularPoint t i • f (angularPoint t) := by
  let K : Set (ℝ × ℝ) := Icc (0, -Real.pi) (1, Real.pi)
  let D := fun z => fderiv ℝ f z (EuclideanSpace.single i 1)
  have hD : Continuous D := (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨hR, hT⟩ := m64DiskFlux_contDiff hf i
  have hc : Continuous (fun p : ℝ × ℝ =>
      fderiv ℝ (m64DiskRadialFlux f i) p (1, 0) +
        fderiv ℝ (m64DiskAngularFlux f i) p (0, 1)) :=
    ((hR.continuous_fderiv (by simp)).clm_apply continuous_const).add
      ((hT.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hgreen := integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    (m64DiskRadialFlux f i) (m64DiskAngularFlux f i)
    (fderiv ℝ (m64DiskRadialFlux f i)) (fderiv ℝ (m64DiskAngularFlux f i))
    (0, -Real.pi) (1, Real.pi) ⟨zero_le_one, hpi⟩
    hR.continuous.continuousOn hT.continuous.continuousOn
    (fun p _ => (hR.differentiable (by simp) p).hasFDerivAt)
    (fun p _ => (hT.differentiable (by simp) p).hasFDerivAt)
    (hc.continuousOn.integrableOn_compact isCompact_Icc)
  have hends : (fun r => m64DiskAngularFlux f i (r, Real.pi)) =
      (fun r => m64DiskAngularFlux f i (r, -Real.pi)) :=
    funext (m64DiskAngularFlux_endpoints f i)
  have hzero : (fun t => m64DiskRadialFlux f i (0, t)) = (fun _ => (0 : E)) := by
    funext t
    simp [m64DiskRadialFlux]
  have hone : (fun t => m64DiskRadialFlux f i (1, t)) =
      (fun t => angularPoint t i • f (angularPoint t)) := by
    funext t
    simp only [m64DiskRadialFlux, one_mul, one_smul]
  simp only [hends, sub_self, zero_add, hzero, hone, intervalIntegral.integral_zero,
    sub_zero] at hgreen
  have hsets : Ioc (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi =ᵐ[volume] K := by
    change Ioc (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi =ᵐ[volume.prod volume] K
    simpa only [K, ← Icc_prod_Icc] using
      (Measure.set_prod_ae_eq (μ := volume) (ν := volume)
        (Ioc_ae_eq_Icc : Ioc (0 : ℝ) 1 =ᵐ[volume] Icc 0 1)
        (Ioo_ae_eq_Icc : Ioo (-Real.pi) Real.pi =ᵐ[volume] Icc (-Real.pi) Real.pi))
  calc
    _ = ∫ p in Ioc (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • D (p.1 • angularPoint p.2) := m64Integral_loopDisk_polar_vector D hD
    _ = ∫ p in K, p.1 • D (p.1 • angularPoint p.2) := setIntegral_congr_set hsets
    _ = ∫ p in K, fderiv ℝ (m64DiskRadialFlux f i) p (1, 0) +
        fderiv ℝ (m64DiskAngularFlux f i) p (0, 1) :=
      integral_congr_ae (Eventually.of_forall (fun p => (m64DiskFlux_divergence hf i p).symm))
    _ = ∫ t in -Real.pi..Real.pi, angularPoint t i • f (angularPoint t) := hgreen
    _ = _ := by rw [intervalIntegral.integral_of_le hpi, integral_Icc_eq_integral_Ioc]

theorem m64Disk_green_identity {f : LoopPlane → E} {phi : LoopPlane → ℝ}
    (hf : ContDiff ℝ 1 f) (hphi : ContDiff ℝ 1 phi) (i : Fin 2) :
    (∫ z in loopDiskSet, phi z • fderiv ℝ f z (EuclideanSpace.single i 1)) +
      (∫ z in loopDiskSet, fderiv ℝ phi z (EuclideanSpace.single i 1) • f z) =
        ∫ t in Icc (-Real.pi) Real.pi,
          angularPoint t i • (phi (angularPoint t) • f (angularPoint t)) := by
  let v : LoopPlane := EuclideanSpace.single i 1
  have hleft : IntegrableOn (fun z => phi z • fderiv ℝ f z v) loopDiskSet volume :=
    (hphi.continuous.smul ((hf.continuous_fderiv (by simp)).clm_apply continuous_const))
      |>.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)
  have hright : IntegrableOn (fun z => fderiv ℝ phi z v • f z) loopDiskSet volume :=
    (((hphi.continuous_fderiv (by simp)).clm_apply continuous_const).smul hf.continuous)
      |>.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)
  have hprod (z : LoopPlane) :
      fderiv ℝ (fun p => phi p • f p) z v =
        phi z • fderiv ℝ f z v + fderiv ℝ phi z v • f z := by
    rw [fderiv_fun_smul (hphi.differentiable (by simp) z) (hf.differentiable (by simp) z),
      add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [← integral_add hleft hright]
  calc
    _ = ∫ z in loopDiskSet, fderiv ℝ (fun p => phi p • f p) z v :=
      integral_congr_ae (Eventually.of_forall (fun z => (hprod z).symm))
    _ = _ := m64Disk_integral_partial (hphi.smul hf) i

end PoincareConjecture
