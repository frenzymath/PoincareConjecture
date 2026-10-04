import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# A product cylinder inside a centered chart

The closed-ball neighborhood basis and the maximum product metric give
a positive closed cylinder inside the chart target. Source: M53
derivation 12, for the excision comparison in the separation repair of
Morgan--Tian, Proposition 15.12 and Remark 15.13, p. 365.
-/

set_option autoImplicit false

open Set Metric
open scoped Topology

namespace OpenPartialHomeomorph

/-- A chart target containing zero contains a positive closed cylinder.
No properness hypothesis is needed for this containment. Source: M53
derivation 12, for Morgan--Tian, p. 365. -/
theorem exists_pos_cylinder_subset_target
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    (e : OpenPartialHomeomorph X (E × ℝ)) (h0 : (0 : E × ℝ) ∈ e.target) :
    ∃ r : ℝ, 0 < r ∧ closedBall (0 : E) r ×ˢ Icc (-r) r ⊆ e.target := by
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp (e.open_target.mem_nhds h0)
  refine ⟨r, hr, ?_⟩
  rwa [← Real.closedBall_zero_eq_Icc, closedBall_prod_same]

end OpenPartialHomeomorph
