import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Set.Finite.Basic

set_option autoImplicit false

open Set Metric
open scoped Topology

namespace Set.Finite

theorem exists_strict_sign_preserving_radius
    {E : Type*} [MetricSpace E] {V : Set E} (hV : V.Finite)
    {f : E → ℝ} (hf : Continuous f) :
    ∃ δ > 0, ∀ v ∈ V, ∀ y, dist y v < δ →
      (f v < 0 → f y < 0) ∧ (0 < f v → 0 < f y) := by
  have hpoint (v : E) : ∃ δ > 0, ∀ y, dist y v < δ →
      (f v < 0 → f y < 0) ∧ (0 < f v → 0 < f y) := by
    rcases lt_trichotomy (f v) 0 with hn | hz | hp
    · obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
        ((isOpen_lt hf continuous_const).mem_nhds hn)
      exact ⟨δ, hδ, fun y hy => ⟨fun _ => hball hy, fun h => (hn.not_gt h).elim⟩⟩
    · exact ⟨1, zero_lt_one, fun y _ => ⟨fun h => ((hz ▸ h).false).elim,
        fun h => ((hz ▸ h).false).elim⟩⟩
    · obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
        ((isOpen_lt continuous_const hf).mem_nhds hp)
      exact ⟨δ, hδ, fun y hy => ⟨fun h => (hp.not_gt h).elim, fun _ => hball hy⟩⟩
  induction V, hV using Set.Finite.induction_on with
  | empty => exact ⟨1, zero_lt_one, fun _ h => h.elim⟩
  | @insert v V hv hV ih =>
    obtain ⟨δ, hδ, hδall⟩ := ih
    obtain ⟨η, hη, hηall⟩ := hpoint v
    refine ⟨min δ η, lt_min hδ hη, ?_⟩
    intro x hx y hy
    rcases hx with rfl | hx
    · exact hηall y (hy.trans_le (min_le_right _ _))
    · exact hδall x hx y (hy.trans_le (min_le_left _ _))

end Set.Finite
