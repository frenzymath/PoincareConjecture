import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_Normalization
import PoincareConjecture.Proofs.M04.ScalarEvolution
import Mathlib.Analysis.Calculus.Deriv.MeanValue









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M45NeckGluingInput

variable {epsilon beta : ℝ} (I : M45NeckGluingInput.{u} epsilon beta)




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

end PoincareConjecture.M45NeckGluingInput
