import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.OpenPartialHomeomorph.Basic

set_option autoImplicit false

open Set Metric
open scoped Topology

namespace OpenPartialHomeomorph

theorem exists_pos_cylinder_subset_target
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    (e : OpenPartialHomeomorph X (E × ℝ)) (h0 : (0 : E × ℝ) ∈ e.target) :
    ∃ r : ℝ, 0 < r ∧ closedBall (0 : E) r ×ˢ Icc (-r) r ⊆ e.target := by
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp (e.open_target.mem_nhds h0)
  refine ⟨r, hr, ?_⟩
  rwa [← Real.closedBall_zero_eq_Icc, closedBall_prod_same]

end OpenPartialHomeomorph
