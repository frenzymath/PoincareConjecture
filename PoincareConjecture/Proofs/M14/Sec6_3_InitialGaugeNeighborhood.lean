import PoincareConjecture.Proofs.M14.Mathlib.InitialFamilyNeighborhood
import PoincareConjecture.Proofs.M14.Sec6_2_GaugeLift

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_smooth_initial_gaugeFamily
    (b : G.gaugeCover.index)
    (t₀ : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x₀ : G.gaugeCover.spatial b)
    {U : Set E} (hU : IsOpen U) {z₀ : E} (hz₀ : z₀ ∈ U) {S : ℝ} (hS : 0 < S)
    (γ : E × ℝ → G.Point)
    (hγ : ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ γ
      (U ×ˢ Icc 0 S))
    (hzero : ∀ A ∈ U, γ (A, 0) = (G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)) :
    ∃ V : Set E, IsOpen V ∧ z₀ ∈ V ∧ V ⊆ U ∧ ∃ d : ℝ, 0 < d ∧ d ≤ S ∧
      ∃ β : E × ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
          G.gaugeCover.spatial b,
        ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ β (V ×ˢ Icc 0 d) ∧
        (∀ z ∈ V ×ˢ Icc 0 d, (G.gaugeCover.cylinder b).toSpacetime (β z) = γ z) ∧
        (∀ z ∈ V ×ˢ Icc 0 d, (β z).1.val = G.spacetime.timeFunction (γ z)) ∧
        ∀ A ∈ V, β (A, 0) = (t₀, x₀) := by
  let h := G.gaugeCover.local_diffeomorph b (t₀, x₀)
  have hz : γ (z₀, 0) ∈ h.localInverse.source := by
    rw [hzero z₀ hz₀]
    exact h.localInverse_mem_source
  have hnear : γ ⁻¹' h.localInverse.source ∈ 𝓝[U ×ˢ Icc 0 S] (z₀, 0) :=
    (hγ.continuousOn (z₀, 0) ⟨hz₀, le_rfl, hS.le⟩).preimage_mem_nhdsWithin
      (h.localInverse_open_source.mem_nhds hz)
  obtain ⟨V, hV, hzV, hVU, d, hd, hdS, hmap⟩ :=
    exists_open_initial_family_neighborhood hU hz₀ hS hnear
  refine ⟨V, hV, hzV, hVU, d, hd, hdS, h.localInverse ∘ γ,
    h.localInverse_contMDiffOn.comp
      (hγ.mono (prod_mono hVU (Icc_subset_Icc le_rfl hdS))) hmap, ?_, ?_, ?_⟩
  · intro z hz
    exact h.localInverse_right_inv (hmap hz)
  · intro z hz
    exact ((G.gaugeCover.cylinder b).time_eq (h.localInverse (γ z))).symm.trans
      (congrArg G.spacetime.timeFunction (h.localInverse_right_inv (hmap hz)))
  · intro A hA
    change h.localInverse (γ (A, 0)) = (t₀, x₀)
    rw [hzero A (hVU hA)]
    exact h.localInverse_left_inv h.localInverse_mem_target

end PoincareConjecture.M14
