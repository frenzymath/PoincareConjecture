import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.Branch.RegularizedKernel

/-!
# The actual L1 error of the continuous Cauchy kernels

The difference is supported in its actual small disk, and the exact
translated radial integral bounds its L1 norm. Source: M65 derivation
32, shared half-disk matrix tool, for MT Lemma 19.2, printed pp. 438--439;
Eschenburg--Tribuzy, Cauchy--Riemann inequalities, preprint pp. 8--11.
-/

set_option autoImplicit false

open Set MeasureTheory Metric
open scoped Topology

namespace PoincareMT.M65Branch

/-- The genuine translated kernel error is integrable and has the
uniform L1 bound needed to pass to the singular operator. Source:
derivation 32, shared half-disk tool, for MT 19.2, pp. 438--439. -/
theorem kernelError_integrable_bound {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    Integrable (fun w : ℂ => (z - w)⁻¹ - regularizedCauchyKernel δ (z - w)) ∧
      (∫ w : ℂ, ‖(z - w)⁻¹ - regularizedCauchyKernel δ (z - w)‖) ≤
        4 * Real.pi * δ := by
  let b (w : ℂ) := (ball z δ).indicator (fun w => 2 * ‖z - w‖⁻¹) w
  have hb : Integrable b := by
    apply (integrable_indicator_iff measurableSet_ball).mpr
    have hk := IntegrableOn.mono_set
      ((locallyIntegrable_cauchyKernel_sub z).integrableOn_isCompact
        (isCompact_closedBall z δ)).norm ball_subset_closedBall
    simpa only [norm_inv, IntegrableOn] using hk.const_mul 2
  have hm : AEStronglyMeasurable
      (fun w : ℂ => (z - w)⁻¹ - regularizedCauchyKernel δ (z - w)) volume :=
    ((measurable_const.sub measurable_id).inv.aestronglyMeasurable).sub
      (((continuous_regularizedCauchyKernel hδ).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable)
  have hbound (w : ℂ) : ‖(z - w)⁻¹ - regularizedCauchyKernel δ (z - w)‖ ≤ b w := by
    have hh := norm_sub_regularizedCauchyKernel_le hδ (z - w)
    have heq : z - w ∈ ball (0 : ℂ) δ ↔ w ∈ ball z δ := by
      simp only [mem_ball, dist_eq_norm, sub_zero, norm_sub_rev]
    by_cases hw : w ∈ ball z δ
    · simpa only [b, indicator_of_mem hw, indicator_of_mem (heq.mpr hw)] using hh
    · have hw' : z - w ∉ ball (0 : ℂ) δ := fun h => hw (heq.mp h)
      simpa only [b, indicator_of_notMem hw, indicator_of_notMem hw'] using hh
  have hi := hb.mono' hm (ae_of_all _ hbound)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ w, b w := integral_mono_ae hi.norm hb (ae_of_all _ hbound)
    _ = 2 * (2 * Real.pi * δ) := by
      rw [integral_indicator measurableSet_ball, integral_const_mul,
        integral_norm_inv_ball_center z hδ.le]
    _ = _ := by ring

end PoincareMT.M65Branch
