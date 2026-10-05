import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Uniform thickening of a compact slice set

An open neighborhood of the image of a compact zero section
contains a uniformly thick closed parameter neighborhood.
This chooses the full-slice parameters in Cairns' recurrence,
pp. 804--805; see M76 derivation 61.
-/

set_option autoImplicit false

open Set
open scoped Topology

variable {X Y Z : Type*} [TopologicalSpace X] [NormedAddCommGroup Y] [TopologicalSpace Z]

/-- A compact zero section has a uniform positive closed-ball
parameter thickening inside any prescribed open image neighborhood.
See Cairns pp. 804--805 and M76 derivation 61. -/
theorem Continuous.exists_pos_closedBall_thickening {f : X × Y → Z} (hf : Continuous f)
    {C : Set X} (hC : IsCompact C) {U : Set Z} (hU : IsOpen U)
    (hzero : ∀ x ∈ C, f (x, 0) ∈ U) :
    ∃ r : ℝ, 0 < r ∧ MapsTo f (C ×ˢ Metric.closedBall (0 : Y) r) U := by
  have hz : C ×ˢ ({0} : Set Y) ⊆ f ⁻¹' U := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    rw [mem_singleton_iff] at hy
    change y = 0 at hy
    subst y
    exact hzero x hx
  obtain ⟨O, V, _, hV, hCO, h0V, hOV⟩ :=
    generalized_tube_lemma hC isCompact_singleton (hU.preimage hf) hz
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (h0V (mem_singleton 0)))
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro z hz
  exact hOV ⟨hCO hz.1, hball (Metric.closedBall_subset_ball (half_lt_self hr) hz.2)⟩
