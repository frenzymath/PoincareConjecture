import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialDiskGreen
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeAffine
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakReplacementIntegration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped ContDiff

namespace PoincareConjecture

open Proofs.M58 Poincare.Analysis.Sobolev.Weak

local notation "S" => ball (0 : LoopPlane) 1
local notation "mu" => volume.restrict S

theorem m64ContinuousScalarH1Disk_green
    {u : LoopPlane → ℝ} {V : Fin 2 → LoopPlane → ℝ}
    (hu : MemLp u 2 mu) (hV : ∀ i, MemLp (V i) 2 mu)
    (hw : ∀ i, HasWeakPartialDeriv i (V i) u S) (hc : Continuous u)
    (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) (i : Fin 2) :
    (∫ p in S, phi p * V i p) +
      (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) * u p) =
      ∫ t in Icc (-Real.pi) Real.pi,
        angularPoint t i * (phi (angularPoint t) * u (angularPoint t)) := by
  let U : LoopPlane → EuclideanSpace ℝ (Fin 1) :=
    fun p => (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => u p)
  let W : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin 1) :=
    fun i p => (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => V i p)
  have hU : MemLp U 2 mu := MemLp.of_eval_piLp (fun _ => hu)
  have hW (i : Fin 2) : MemLp (W i) 2 mu := MemLp.of_eval_piLp (fun _ => hV i)
  have hUc : Continuous U :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℝ)).comp (continuous_pi fun _ => hc)
  have hgreen := m64ContinuousH1Disk_green U W hU hW
    (fun i _ => hw i) hUc.continuousOn phi hphi i
  have htest {f : LoopPlane → ℝ} (hf : Continuous f) : MemLp f 2 mu := by
    apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
    exact (hf.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : LoopPlane) 1) |>.mono_set ball_subset_closedBall
  have hIV := m64L2_test_integrable (hW i) (htest hphi.continuous)
  have hIU := m64L2_test_integrable hU (htest
    ((hphi.continuous_fderiv (by simp)).clm_apply
      (continuous_const (y := EuclideanSpace.single i 1))))
  have hIR : IntegrableOn (fun t : ℝ => angularPoint t i •
      (phi (angularPoint t) • U (angularPoint t))) (Icc (-Real.pi) Real.pi) :=
    (((EuclideanSpace.proj i).continuous.comp contDiff_angularPoint.continuous).smul
      ((hphi.continuous.comp contDiff_angularPoint.continuous).smul
        (hUc.comp contDiff_angularPoint.continuous))).continuousOn.integrableOn_compact
      isCompact_Icc
  let T : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ := EuclideanSpace.proj 0
  have hproj := congrArg T hgreen
  simp only [map_add] at hproj
  rw [← T.integral_comp_comm hIV, ← T.integral_comp_comm hIU,
    ← T.integral_comp_comm hIR] at hproj
  simpa +instances only [T, Function.comp_apply, map_smul, EuclideanSpace.coe_proj,
    U, W, smul_eq_mul] using! hproj

theorem m64ContinuousScalarH1Disk_affine_green
    {u : LoopPlane → ℝ} {V : Fin 2 → LoopPlane → ℝ}
    (hu : MemLp u 2 mu) (hV : ∀ i, MemLp (V i) 2 mu)
    (hw : ∀ i, HasWeakPartialDeriv i (V i) u S) (hc : Continuous u)
    (a : LoopPlane) {r : ℝ} (hr : 0 < r)
    (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) (i : Fin 2) :
    (∫ p in ball a r, phi p * (r⁻¹ * V i (m64ConeNormalize a r p))) +
      (∫ p in ball a r, fderiv ℝ phi p (EuclideanSpace.single i 1) *
        u (m64ConeNormalize a r p)) =
      r * ∫ t in Icc (-Real.pi) Real.pi,
        angularPoint t i * (phi (a + r • angularPoint t) * u (angularPoint t)) := by
  let psi := fun z : LoopPlane => phi (a + r • z)
  have hpsi : ContDiff ℝ 1 psi :=
    hphi.comp (contDiff_const.add (contDiff_id.const_smul r))
  have hd (z : LoopPlane) : fderiv ℝ psi z (EuclideanSpace.single i 1) =
      r * fderiv ℝ phi (a + r • z) (EuclideanSpace.single i 1) := by
    rw [show psi = (fun z : LoopPlane => phi (a + r • z)) from rfl, M60.suRescale_fderiv]
    rfl
  have hleft : (∫ p in ball a r, phi p * (r⁻¹ * V i (m64ConeNormalize a r p))) =
      r * ∫ z in S, psi z * V i z := by
    rw [m64ConeAffine_integral _ a hr, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    simp only [m64ConeNormalize_apply a hr, smul_eq_mul, psi]
    field_simp [hr.ne']
  have hright : (∫ p in ball a r, fderiv ℝ phi p (EuclideanSpace.single i 1) *
      u (m64ConeNormalize a r p)) =
      r * ∫ z in S, fderiv ℝ psi z (EuclideanSpace.single i 1) * u z := by
    rw [m64ConeAffine_integral _ a hr, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    simp only [m64ConeNormalize_apply a hr, hd, smul_eq_mul]
    ring
  rw [hleft, hright, ← mul_add, m64ContinuousScalarH1Disk_green hu hV hw hc psi hpsi i]

end PoincareConjecture
