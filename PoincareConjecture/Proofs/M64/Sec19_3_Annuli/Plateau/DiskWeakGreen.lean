import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.DiskGreenRescaling
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.StrongSquarePairing
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.UniformCircleIntegral











set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

open Proofs.M58

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]



theorem m64Disk_weak_green_of_strong_approximation
    (a : LoopPlane) {r : ℝ} (hr : 0 < r)
    (f : ℕ → LoopPlane → E) (hf : ∀ j, ContDiff ℝ 1 (f j))
    (u : LoopPlane → E) (V : Fin 2 → LoopPlane → E) (gamma : ℝ → E)
    (hu : MemLp u 2 (volume.restrict (Metric.closedBall a r)))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict (Metric.closedBall a r)))
    (hval : Tendsto (fun j => ∫ p in Metric.closedBall a r, ‖f j p - u p‖ ^ 2)
      atTop (𝓝 0))
    (hcol : ∀ i, Tendsto (fun j => ∫ p in Metric.closedBall a r,
      ‖fderiv ℝ (f j) p (EuclideanSpace.single i 1) - V i p‖ ^ 2) atTop (𝓝 0))
    (htrace : TendstoUniformlyOn (fun j t => f j (a + r • angularPoint t)) gamma
      atTop (Icc (-Real.pi) Real.pi))
    (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) (i : Fin 2) :
    (∫ p in Metric.closedBall a r, phi p • V i p) +
      (∫ p in Metric.closedBall a r,
        fderiv ℝ phi p (EuclideanSpace.single i 1) • u p) =
      r • ∫ t in Icc (-Real.pi) Real.pi,
        angularPoint t i • (phi (a + r • angularPoint t) • gamma t) := by
  let K := Metric.closedBall a r
  let D := fun j p => fderiv ℝ (f j) p (EuclideanSpace.single i 1)
  let dphi := fun p => fderiv ℝ phi p (EuclideanSpace.single i 1)
  have hcD (j : ℕ) : Continuous (D j) :=
    ((hf j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hcdphi : Continuous dphi :=
    (hphi.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfl (j : ℕ) : MemLp (f j) 2 (volume.restrict K) := by
    apply (memLp_two_iff_integrable_sq_norm (hf j).continuous.aestronglyMeasurable).mpr
    exact ((hf j).continuous.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall a r)
  have hDl (j : ℕ) : MemLp (D j) 2 (volume.restrict K) := by
    apply (memLp_two_iff_integrable_sq_norm (hcD j).aestronglyMeasurable).mpr
    exact ((hcD j).norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall a r)
  have hpl : MemLp phi 2 (volume.restrict K) := by
    apply (memLp_two_iff_integrable_sq_norm hphi.continuous.aestronglyMeasurable).mpr
    exact (hphi.continuous.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall a r)
  have hdpl : MemLp dphi 2 (volume.restrict K) := by
    apply (memLp_two_iff_integrable_sq_norm hcdphi.aestronglyMeasurable).mpr
    exact (hcdphi.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall a r)
  have hl := (m64StrongSquare_pairing_tendsto D (V i) hDl (hV i) (hcol i) phi hpl).add
    (m64StrongSquare_pairing_tendsto f u hfl hu hval dphi hdpl)
  have hc : Continuous (fun t : ℝ => a + r • angularPoint t) :=
    continuous_const.add (contDiff_angularPoint.continuous.const_smul r)
  let w := fun t : ℝ => angularPoint t i * phi (a + r • angularPoint t)
  have hw : Continuous w :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp contDiff_angularPoint.continuous).mul
      (hphi.continuous.comp hc)
  have hb := m64UniformCircle_weighted_integral_tendsto (neg_le_self Real.pi_pos.le)
    (fun j => ((hf j).continuous.comp hc).continuousOn) htrace w hw.continuousOn
  have hrhs := hb.const_smul r
  have heq (j : ℕ) :
      (∫ p in K, phi p • D j p) + (∫ p in K, dphi p • f j p) =
        r • ∫ t in Icc (-Real.pi) Real.pi, w t • f j (a + r • angularPoint t) := by
    simpa only [K, D, dphi, w, mul_smul] using
      m64Disk_green_identity_rescaled (hf j) hphi a hr i
  have hrhs' : Tendsto
      (fun j => (∫ p in K, phi p • D j p) + (∫ p in K, dphi p • f j p)) atTop
      (𝓝 (r • ∫ t in Icc (-Real.pi) Real.pi,
        angularPoint t i • (phi (a + r • angularPoint t) • gamma t))) := by
    simpa +instances only [heq, w, mul_smul, Function.comp_def] using! hrhs
  exact tendsto_nhds_unique hl hrhs'

end PoincareConjecture
