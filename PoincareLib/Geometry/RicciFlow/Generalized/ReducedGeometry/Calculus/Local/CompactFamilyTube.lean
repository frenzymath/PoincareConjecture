import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Compactness.Compact

/-!
# A uniform parameter neighborhood for a compact relative family

The compact tube step in Morgan-Tian Proposition 6.30, pp. 118-119.
Continuity on a compact time set times an open parameter set suffices;
the time set need not itself be open.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareMT.M14

variable {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]

/-- A continuous compact family staying in an open target at one
parameter stays there throughout one open parameter neighborhood,
the relative compact tube step in Proposition 6.30, pp. 118-119. -/
theorem exists_open_parameter_tube {K : Set A} {U : Set B} {V : Set C}
    {f : A × B → C} (hK : IsCompact K) (hU : IsOpen U)
    (hf : ContinuousOn f (K ×ˢ U)) (hV : IsOpen V)
    {b : B} (hb : b ∈ U) (hcenter : ∀ a ∈ K, f (a, b) ∈ V) :
    ∃ N : Set B, IsOpen N ∧ b ∈ N ∧ N ⊆ U ∧ ∀ a ∈ K, ∀ y ∈ N, f (a, y) ∈ V := by
  obtain ⟨Ω, hΩ, heq⟩ := continuousOn_iff'.mp hf V hV
  have hΩcenter (a : A) (ha : a ∈ K) : (a, b) ∈ Ω := by
    have hz : (a, b) ∈ f ⁻¹' V ∩ (K ×ˢ U) := ⟨hcenter a ha, ha, hb⟩
    rw [heq] at hz
    exact hz.1
  have hnear : ∀ᶠ y in 𝓝 b, ∀ a ∈ K, (a, y) ∈ Ω := by
    apply hK.eventually_forall_of_forall_eventually
    intro a ha
    exact (hΩ.preimage continuous_swap).mem_nhds (hΩcenter a ha)
  obtain ⟨N, hNsub, hN, hbN⟩ := mem_nhds_iff.mp hnear
  refine ⟨N ∩ U, hN.inter hU, ⟨hbN, hb⟩, inter_subset_right, ?_⟩
  intro a ha y hy
  have hz : (a, y) ∈ Ω ∩ (K ×ˢ U) := ⟨hNsub hy.1 a ha, ha, hy.2⟩
  rw [← heq] at hz
  exact hz.1

end PoincareMT.M14
