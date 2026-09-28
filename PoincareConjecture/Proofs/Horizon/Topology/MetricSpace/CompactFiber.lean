import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Instances.Real.Lemmas



set_option autoImplicit false

open Set Metric Filter
open scoped Topology

namespace Poincare.Topology



theorem exists_closedBand_subset_of_fiber_subset_open
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {h : X → Real} (hh : Continuous h) {c : Real}
    {U : Set X} (hU : IsOpen U) (hlevel : h ⁻¹' {c} ⊆ U) :
    ∃ δ : Real, 0 < δ ∧ h ⁻¹' Icc (c - δ) (c + δ) ⊆ U := by
  have hevent : ∀ᶠ t in 𝓝 c, ∀ x ∈ h ⁻¹' {t}, x ∈ U :=
    hh.isClosedMap.eventually_nhds_fiber c (fun x hx => hU.mem_nhds (hlevel hx))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro x hx
  apply hball (show h x ∈ ball c ε from ?_) x rfl
  rw [mem_ball, Real.dist_eq]
  have habs : |h x - c| ≤ ε / 2 :=
    abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  exact habs.trans_lt (by linarith)

end Poincare.Topology
