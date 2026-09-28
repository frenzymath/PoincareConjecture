import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.DiskGreenRescaling
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.UniformCircleIntegral
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.WeakCompactness.DerivativeLimit
import PoincareConjecture.Proofs.M60.Mathlib.NullSphere












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

open Proofs.M58 Poincare.Analysis.Sobolev.WeakCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]



theorem m64Disk_green_of_weak_limits
    (a : LoopPlane) {r : ℝ} (hr : 0 < r)
    (f : ℕ → LoopPlane → E) (hf : ∀ j, ContDiff ℝ 1 (f j))
    (U D : ℕ → Lp E 2 (volume.restrict (Metric.ball a r)))
    (u v : Lp E 2 (volume.restrict (Metric.ball a r)))
    (hu : WeakConverges U u) (hv : WeakConverges D v) (i : Fin 2)
    (hU : ∀ j, (U j : LoopPlane → E) =ᵐ[volume.restrict (Metric.ball a r)] f j)
    (hD : ∀ j, (D j : LoopPlane → E) =ᵐ[volume.restrict (Metric.ball a r)]
      (fun p => fderiv ℝ (f j) p (EuclideanSpace.single i 1)))
    (gamma : ℝ → E)
    (htrace : TendstoUniformlyOn (fun j t => f j (a + r • angularPoint t)) gamma
      atTop (Icc (-Real.pi) Real.pi))
    (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) :
    (∫ p in Metric.ball a r, phi p • v p) +
      (∫ p in Metric.ball a r, fderiv ℝ phi p (EuclideanSpace.single i 1) • u p) =
      r • ∫ t in Icc (-Real.pi) Real.pi,
        angularPoint t i • (phi (a + r • angularPoint t) • gamma t) := by
  let dphi := fun p => fderiv ℝ phi p (EuclideanSpace.single i 1)
  have hdc : Continuous dphi :=
    (hphi.continuous_fderiv (by simp)).clm_apply continuous_const
  have hp : MemLp phi 2 (volume.restrict (Metric.ball a r)) := by
    apply (memLp_two_iff_integrable_sq_norm hphi.continuous.aestronglyMeasurable).mpr
    exact (hphi.continuous.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall a r) |>.mono_set Metric.ball_subset_closedBall
  have hdp : MemLp dphi 2 (volume.restrict (Metric.ball a r)) := by
    apply (memLp_two_iff_integrable_sq_norm hdc.aestronglyMeasurable).mpr
    exact (hdc.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall a r) |>.mono_set Metric.ball_subset_closedBall
  have hc : Continuous (fun t : ℝ => a + r • angularPoint t) :=
    continuous_const.add (contDiff_angularPoint.continuous.const_smul r)
  let w := fun t : ℝ => angularPoint t i * phi (a + r • angularPoint t)
  have hw : Continuous w :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp contDiff_angularPoint.continuous).mul
      (hphi.continuous.comp hc)
  have hboundary := (m64UniformCircle_weighted_integral_tendsto
    (neg_le_self Real.pi_pos.le) (fun j => ((hf j).continuous.comp hc).continuousOn)
    htrace w hw.continuousOn).const_smul r
  have hseq (j : ℕ) :
      testIntegral phi hp (D j) + testIntegral dphi hdp (U j) =
        r • ∫ t in Icc (-Real.pi) Real.pi, w t • f j (a + r • angularPoint t) := by
    rw [testIntegral_apply, testIntegral_apply]
    have h0 : (∫ p in Metric.ball a r, phi p • D j p) =
        ∫ p in Metric.ball a r, phi p • fderiv ℝ (f j) p (EuclideanSpace.single i 1) :=
      integral_congr_ae ((hD j).mono fun p hp => congrArg (fun z => phi p • z) hp)
    have h1 : (∫ p in Metric.ball a r, dphi p • U j p) =
        ∫ p in Metric.ball a r, dphi p • f j p :=
      integral_congr_ae ((hU j).mono fun p hp => congrArg (fun z => dphi p • z) hp)
    rw [h0, h1,
      setIntegral_congr_set (M60.haar_ball_ae_eq_closedBall volume a r),
      setIntegral_congr_set (M60.haar_ball_ae_eq_closedBall volume a r)]
    simpa only [dphi, w, mul_smul] using
      m64Disk_green_identity_rescaled (hf j) hphi a hr i
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro L
  have hl := (hv (L.comp (testIntegral phi hp))).add
    (hu (L.comp (testIntegral dphi hdp)))
  have hrhs := (L.continuous.tendsto _).comp hboundary
  have heq (j : ℕ) : L (testIntegral phi hp (D j)) + L (testIntegral dphi hdp (U j)) =
      L (r • ∫ t in Icc (-Real.pi) Real.pi, w t • f j (a + r • angularPoint t)) := by
    rw [← map_add, hseq]
  have hrhs' : Tendsto
      (fun j => L (testIntegral phi hp (D j)) + L (testIntegral dphi hdp (U j))) atTop
      (𝓝 (L (r • ∫ t in Icc (-Real.pi) Real.pi, w t • gamma t))) := by
    simpa +instances only [Function.comp_def, heq] using! hrhs
  simpa only [ContinuousLinearMap.comp_apply, ← map_add, testIntegral_apply, dphi,
    w, mul_smul] using tendsto_nhds_unique hl hrhs'

end PoincareConjecture
