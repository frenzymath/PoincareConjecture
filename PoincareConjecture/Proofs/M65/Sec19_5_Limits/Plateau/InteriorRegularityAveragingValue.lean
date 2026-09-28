import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityAveragingDerivative
import Mathlib.Analysis.Calculus.ContDiff.Convolution

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology ContDiff Convolution

namespace PoincareConjecture.M65Interior

noncomputable def averagingValue (u : LoopPlane → ℝ) (r : ℝ) (x : LoopPlane) : ℝ :=
  ∫ z, u z * averagingKernel r (x - z)

private theorem averagingKernel_parameters (r : ℝ) :
    (∀ s z, s ∈ Ioo 0 (2 * r) → z ∉ closedBall (0 : LoopPlane) (2 * r) →
      averagingKernel s z = 0) ∧
    ContDiffOn ℝ ∞ (Function.uncurry averagingKernel) (Ioo 0 (2 * r) ×ˢ univ) := by
  constructor
  · intro s z hs hz
    by_contra hne
    exact hz (closedBall_subset_closedBall hs.2.le (averagingKernel_support hs.1 hne))
  · intro p hp
    exact (averagingKernel_joint_contDiffAt hp.1.1.ne').contDiffWithinAt

theorem averagingValue_integrable {u : LoopPlane → ℝ} (hu : LocallyIntegrable u volume)
    {r : ℝ} (hr : 0 < r) (x : LoopPlane) :
    Integrable (fun z => u z * averagingKernel r (x - z)) := by
  exact (averagingKernel_hasCompactSupport hr).convolutionExists_right
    (ContinuousLinearMap.mul ℝ ℝ) hu (averagingKernel_contDiff r).continuous x

theorem averagingValue_joint_contDiffAt {u : LoopPlane → ℝ}
    (hu : LocallyIntegrable u volume) {r : ℝ} (hr : 0 < r) (x : LoopPlane) :
    ContDiffAt ℝ ∞ (fun p : ℝ × LoopPlane => averagingValue u p.1 p.2) (r, x) := by
  obtain ⟨hzero, hsmooth⟩ := averagingKernel_parameters r
  have h := contDiffOn_convolution_right_with_param (ContinuousLinearMap.mul ℝ ℝ)
    isOpen_Ioo (isCompact_closedBall (0 : LoopPlane) (2 * r)) hzero hu hsmooth
  exact h.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
    ⟨⟨hr, by linarith⟩, mem_univ x⟩)

theorem averagingValue_joint_hasFDerivAt {u : LoopPlane → ℝ}
    (hu : LocallyIntegrable u volume) {r : ℝ} (hr : 0 < r) (x : LoopPlane) :
    HasFDerivAt (fun p : ℝ × LoopPlane => averagingValue u p.1 p.2)
      ((u ⋆[(ContinuousLinearMap.mul ℝ ℝ).precompR (ℝ × LoopPlane), volume]
        fun z => fderiv ℝ (Function.uncurry averagingKernel) (r, z)) x) (r, x) := by
  obtain ⟨hzero, hsmooth⟩ := averagingKernel_parameters r
  exact hasFDerivAt_convolution_right_with_param (ContinuousLinearMap.mul ℝ ℝ)
    isOpen_Ioo (isCompact_closedBall (0 : LoopPlane) (2 * r)) hzero hu
    (hsmooth.of_le (by simp)) (r, x) ⟨hr, by linarith⟩

private theorem averagingValue_joint_derivative_integrable {u : LoopPlane → ℝ}
    (hu : LocallyIntegrable u volume) {r : ℝ} (hr : 0 < r) (x : LoopPlane) :
    Integrable (fun z => ((ContinuousLinearMap.mul ℝ ℝ).precompR (ℝ × LoopPlane))
      (u z) (fderiv ℝ (Function.uncurry averagingKernel) (r, x - z))) := by
  obtain ⟨hzero, hsmooth⟩ := averagingKernel_parameters r
  have hc : Continuous (fun z : LoopPlane =>
      fderiv ℝ (Function.uncurry averagingKernel) (r, z)) := by
    apply (hsmooth.continuousOn_fderiv_of_isOpen
      (isOpen_Ioo.prod isOpen_univ) (by simp)).comp_continuous (.prodMk_right _)
    intro z
    exact ⟨⟨hr, by linarith⟩, mem_univ z⟩
  have hs : HasCompactSupport (fun z : LoopPlane =>
      fderiv ℝ (Function.uncurry averagingKernel) (r, z)) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : LoopPlane) (2 * r))
    intro z hz
    apply (hasFDerivAt_zero_of_eventually_const (0 : ℝ) ?_).fderiv
    filter_upwards [((isOpen_Ioo.prod isClosed_closedBall.isOpen_compl).mem_nhds
      (show (r, z) ∈ Ioo 0 (2 * r) ×ˢ (closedBall (0 : LoopPlane) (2 * r))ᶜ from
        ⟨⟨hr, by linarith⟩, hz⟩))] with p hp
    exact hzero p.1 p.2 hp.1 hp.2
  exact hs.convolutionExists_right ((ContinuousLinearMap.mul ℝ ℝ).precompR (ℝ × LoopPlane))
    hu hc x

theorem averagingValue_radius_hasDerivAt {u : LoopPlane → ℝ}
    (hu : LocallyIntegrable u volume) {r : ℝ} (hr : 0 < r) (x : LoopPlane) :
    HasDerivAt (fun s => averagingValue u s x)
      (∫ z, u z * ∑ i : Fin 2, fderiv ℝ (fun y : LoopPlane =>
        ((x i - y i) / r) * averagingKernel r (x - y)) z
          (EuclideanSpace.basisFun (Fin 2) ℝ i)) r := by
  have hcurve : HasDerivAt (fun s : ℝ => (s, x)) (1, 0) r :=
    (hasDerivAt_id r).prodMk (hasDerivAt_const r x)
  apply ((averagingValue_joint_hasFDerivAt hu hr x).comp_hasDerivAt r hcurve).congr_deriv
  rw [convolution, ContinuousLinearMap.integral_apply
    (averagingValue_joint_derivative_integrable hu hr x)]
  apply integral_congr_ae
  filter_upwards with z
  change u z * (fderiv ℝ (Function.uncurry averagingKernel) (r, x - z)) (1, 0) = _
  congr 1
  have hk : DifferentiableAt ℝ (Function.uncurry averagingKernel) (r, x - z) :=
    (averagingKernel_joint_contDiffAt hr.ne').differentiableAt (by simp)
  have hz : HasDerivAt (fun s : ℝ => (s, x - z)) (1, 0) r :=
    (hasDerivAt_id r).prodMk (hasDerivAt_const r (x - z))
  have hd := hk.hasFDerivAt.comp_hasDerivAt r hz
  change HasDerivAt (fun s => averagingKernel s (x - z)) _ r at hd
  exact hd.unique (averagingKernel_radius_weak_test hr.ne' x z)

end PoincareConjecture.M65Interior
