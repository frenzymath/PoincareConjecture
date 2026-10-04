import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Basic

/-!
# Uniform open neighborhoods for compact parameter families

An open condition on a continuous compact family persists on one metric
neighborhood of its parameter. MT2007 Claim 19.1, p. 437;
`2026-09-21-compact-parameter-neighborhood.md`.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareMT.M63

/-- A compact family in an open set remains there on one positive
metric neighborhood of its parameter. MT2007 Claim 19.1, p. 437;
compact parameter neighborhood derivation. No separation or
nonemptiness hypothesis on the compact parameter space is needed. -/
theorem exists_uniform_open_parameter_radius
    {X K Y : Type*} [MetricSpace X] [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace Y] {f : X × K → Y} (hf : Continuous f)
    {O : Set Y} (hO : IsOpen O) {x0 : X} (hx0 : ∀ y : K, f (x0, y) ∈ O) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ x : X, dist x x0 < eps → ∀ y : K, f (x, y) ∈ O := by
  have hnear : ∀ᶠ x in 𝓝 x0, ∀ y ∈ (univ : Set K), f (x, y) ∈ O :=
    isCompact_univ.eventually_forall_of_forall_eventually
      (fun y _ => hf.continuousAt.eventually (hO.mem_nhds (hx0 y)))
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hnear
  exact ⟨eps, heps, fun x hx y => hball hx y (mem_univ _)⟩

end PoincareMT.M63
