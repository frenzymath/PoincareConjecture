import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set
open scoped Topology

namespace Set

variable {X : Type*} [TopologicalSpace X]

theorem IsCompact.exists_pos_abs_le_subset_of_zero_fiber
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) {f : X → ℝ}
    (hf : ContinuousOn f K) (hzero : K ∩ {x | f x = 0} ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, |f x| ≤ δ → x ∈ U := by
  have hcompact : IsCompact (f '' (K \ U)) :=
    (hK.diff hU).image_of_continuousOn (hf.mono sdiff_subset)
  have hnot : (0 : ℝ) ∉ f '' (K \ U) := by
    rintro ⟨x, hx, hfx⟩
    exact hx.2 (hzero ⟨hx.1, hfx⟩)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (hcompact.isClosed.isOpen_compl.mem_nhds hnot)
  refine ⟨ε / 2, by positivity, ?_⟩
  intro x hx hfx
  by_contra hxU
  have hb : f x ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    linarith
  exact hball hb ⟨x, ⟨hx, hxU⟩, rfl⟩

end Set
