import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology InnerProductSpace BoundedContinuousFunction

namespace Poincare.Analysis.Dirichlet.Kernel

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [TopologicalSpace X]

noncomputable def evaluationRow (T : E →L[ℝ] (X →ᵇ ℝ)) (x : X) : E :=
  (InnerProductSpace.toDual ℝ E).symm
    ((BoundedContinuousFunction.evalCLM ℝ x).comp T)

theorem inner_evaluationRow (T : E →L[ℝ] (X →ᵇ ℝ)) (x : X) (f : E) :
    inner ℝ (evaluationRow T x) f = T f x :=
  InnerProductSpace.toDual_symm_apply

theorem norm_evaluationRow_le (T : E →L[ℝ] (X →ᵇ ℝ)) (x : X) :
    ‖evaluationRow T x‖ ≤ ‖T‖ := by
  rw [evaluationRow, (InnerProductSpace.toDual ℝ E).symm.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro f
  exact ((T f).norm_coe_le_norm x).trans (T.le_opNorm f)

omit [CompleteSpace E] in
private theorem continuous_evaluation_comp (T : E →L[ℝ] (X →ᵇ ℝ))
    (hT : IsCompactOperator T) :
    Continuous (fun x => (BoundedContinuousFunction.evalCLM ℝ x).comp T) := by
  have hTc : IsCompactOperator T.toLinearMap := hT
  obtain ⟨K, hK, hTK⟩ := hTc.image_closedBall_subset_compact 1
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have hcont : Continuous (fun p : X × (X →ᵇ ℝ) => dist (p.2 p.1) (p.2 x)) :=
    (continuous_snd.eval continuous_fst).dist (continuous_snd.eval_const x)
  have huniform : ∀ᶠ y in 𝓝 x, ∀ q ∈ K, dist (q y) (q x) < ε / 2 := by
    apply hK.eventually_forall_of_forall_eventually
    intro q _
    have hqcont : ContinuousAt (fun p : X × (X →ᵇ ℝ) => dist (p.2 p.1) (p.2 x))
        (x, q) := hcont.continuousAt
    exact hqcont.eventually (gt_mem_nhds (by simpa using half_pos hε))
  filter_upwards [huniform] with y hy
  rw [dist_eq_norm]
  have hnorm : ‖(BoundedContinuousFunction.evalCLM ℝ y).comp T -
      (BoundedContinuousFunction.evalCLM ℝ x).comp T‖ ≤ ε / 2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (le_of_lt (half_pos hε))
    intro f hf
    have hfball : f ∈ Metric.closedBall (0 : E) 1 := by simpa using hf.le
    have hq := hy (T f) (hTK ⟨f, hfball, rfl⟩)
    simpa only [sub_apply, ContinuousLinearMap.comp_apply,
      BoundedContinuousFunction.evalCLM_apply, dist_eq_norm] using hq.le
  exact hnorm.trans_lt (half_lt_self hε)

theorem continuous_evaluationRow (T : E →L[ℝ] (X →ᵇ ℝ))
    (hT : IsCompactOperator T) : Continuous (evaluationRow T) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.comp (continuous_evaluation_comp T hT)

end Poincare.Analysis.Dirichlet.Kernel
