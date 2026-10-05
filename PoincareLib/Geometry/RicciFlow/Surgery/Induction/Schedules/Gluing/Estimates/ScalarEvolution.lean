import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Gluing.Construction.Normalization
import PoincareLib.Geometry.RicciFlow.Curvature.Evolution.Scalar.Within
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Scalar evolution and the older survival interval

The positive model evolution margin is used through the scalar evolution
equation of the actual recent flow. Its final scalar normalization then
gives the strict scale inequality in Proposition 15.2, pp. 353-354.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M45NeckGluingInput

variable {epsilon beta : ℝ} (I : M45NeckGluingInput.{u} epsilon beta)

/-- A positive scalar evolution margin makes the actual center scalar
strictly increase to its specified final value one. Source: the scalar
curvature argument in Proposition 15.2, pp. 353-354. -/
theorem joining_scalar_lt_one_of_evolution_pos
    (hpos : ∀ t ∈ Ioo (-I.recent_duration) (0 : ℝ),
      0 < (I.recent_flow.connection t).laplacian
        (I.recent_flow.connection t).scalarCurvature I.center +
          2 * (I.recent_flow.connection t).ricciNormSq I.center) :
    (I.recent_flow.connection (-I.recent_duration)).scalarCurvature I.center < 1 := by
  have hmono := strictMonoOn_of_hasDerivWithinAt_pos
    (convex_Icc (-I.recent_duration) (0 : ℝ))
    (I.recent_flow.contDiffOn_scalarCurvature_timeSlice I.center).continuousOn
    (fun t ht => (I.recent_flow.hasDerivWithinAt_scalarCurvature t
      (interior_subset ht) I.center).mono interior_subset)
    (fun t ht => hpos t (by simpa only [interior_Icc] using ht))
  have htime : -I.recent_duration < (0 : ℝ) := neg_lt_zero.mpr I.recent_duration_pos
  simpa only [I.final_scalar_one] using hmono ⟨le_rfl, htime.le⟩ ⟨htime.le, le_rfl⟩ htime

/-- The scalar margin guarantees that the actual older flow begins
strictly before time minus one. Source: Proposition 15.2, pp. 353-354. -/
theorem older_duration_gt_one_of_evolution_pos
    (hpos : ∀ t ∈ Ioo (-I.recent_duration) (0 : ℝ),
      0 < (I.recent_flow.connection t).laplacian
        (I.recent_flow.connection t).scalarCurvature I.center +
          2 * (I.recent_flow.connection t).ricciNormSq I.center) :
    1 < I.older_duration := by
  have hqpos : 0 < (I.recent_flow.connection (-I.recent_duration)).scalarCurvature I.center := by
    rw [← I.joining_scalar_eq]
    exact I.older_neck.neck.scalar_center_pos
  have hq := I.joining_scalar_lt_one_of_evolution_pos hpos
  have hi : 1 < ((I.recent_flow.connection (-I.recent_duration)).scalarCurvature I.center)⁻¹ := by
    simpa only [inv_one] using inv_strictAnti₀ hqpos hq
  have hd := I.older_duration_ge
  rw [I.older_scale_sq] at hd
  linarith [I.recent_duration_pos]

end PoincareMT.M45NeckGluingInput
