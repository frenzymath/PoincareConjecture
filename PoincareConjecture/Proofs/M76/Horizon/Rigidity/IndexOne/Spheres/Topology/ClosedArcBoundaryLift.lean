import Mathlib.Topology.Instances.AddCircle.Real

set_option autoImplicit false
open Set

namespace AddCircle

variable {Y : Type*} [TopologicalSpace Y]

theorem exists_lift_in_closed_arc (period : ℝ) [Fact (0 < period)]
    (f : C(Y, AddCircle period)) (lower upper : ℝ)
    (hlower : 0 < lower) (hupper : upper < period)
    (hrange : ∀ y, f y ∈ ((↑) : ℝ → AddCircle period) '' Icc lower upper) :
    ∃ lift : C(Y, ℝ), (∀ y, (lift y : AddCircle period) = f y) ∧
      ∀ y, lift y ∈ Icc lower upper := by
  let chart := openPartialHomeomorphCoe period (0 : ℝ)
  have hsource {z : ℝ} (hz : z ∈ Icc lower upper) : z ∈ chart.source := by
    change 0 < z ∧ z < 0 + period
    exact ⟨hlower.trans_le hz.1, by simpa using hz.2.trans_lt hupper⟩
  have htarget (y : Y) : f y ∈ chart.target := by
    obtain ⟨z, hz, hzy⟩ := hrange y
    rw [← hzy]
    exact chart.mapsTo (hsource hz)
  let lift : C(Y, ℝ) := ⟨fun y => chart.symm (f y),
    chart.symm.continuousOn.comp_continuous f.continuous htarget⟩
  refine ⟨lift, fun y => chart.right_inv (htarget y), ?_⟩
  intro y
  obtain ⟨z, hz, hzy⟩ := hrange y
  change chart.symm (f y) ∈ Icc lower upper
  rw [← hzy]
  change chart.symm (chart z) ∈ Icc lower upper
  rw [chart.left_inv (hsource hz)]
  exact hz

theorem exists_boundary_lift_in_closed_arc (period : ℝ) [Fact (0 < period)]
    (f : C(Y, AddCircle period)) {A : Set Y} (lower upper : ℝ)
    (hlower : 0 < lower) (hupper : upper < period)
    (hrange : MapsTo f A (((↑) : ℝ → AddCircle period) '' Icc lower upper)) :
    ∃ boundary : C(A, ℝ), (∀ y : A, (boundary y : AddCircle period) = f y) ∧
      ∀ y : A, boundary y ∈ Icc lower upper := by
  exact exists_lift_in_closed_arc period
    ⟨fun y : A => f y, f.continuous.comp continuous_subtype_val⟩
    lower upper hlower hupper (fun y => hrange y.property)

end AddCircle
