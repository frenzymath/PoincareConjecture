import PoincareConjecture.Proofs.M14.Mathlib.ClosedFamilyNeighborhood
import PoincareConjecture.Proofs.M14.Sec6_2_GaugeLift










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





theorem exists_smooth_gaugeFamily_neighborhood {U : Set E} (hU : IsOpen U)
    {z₀ : E} (hz₀ : z₀ ∈ U) {a c s : ℝ} (has : a < s) (hsc : s ≤ c)
    (γ : E × ℝ → G.Point)
    (hγ : ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ γ
      (U ×ˢ Icc a c)) :
    ∃ b : G.gaugeCover.index, ∃ V : Set E, IsOpen V ∧ z₀ ∈ V ∧ V ⊆ U ∧
      ∃ l r : ℝ, a < l ∧ l < s ∧ s ≤ r ∧ r ≤ c ∧ Icc l r ∈ 𝓝[Icc a c] s ∧
      ∃ β : E × ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
          G.gaugeCover.spatial b,
        ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ β
          (V ×ˢ Icc l r) ∧
        (∀ z ∈ V ×ˢ Icc l r, (G.gaugeCover.cylinder b).toSpacetime (β z) = γ z) ∧
        ∀ z ∈ V ×ˢ Icc l r, (β z).1.val = G.spacetime.timeFunction (γ z) := by
  obtain ⟨b, N, lift, hN, hpN, hlift, hright, hclock⟩ :=
    exists_smooth_gauge_lift G (γ (z₀, s))
  have hnear : γ ⁻¹' N ∈ 𝓝[U ×ˢ Icc a c] (z₀, s) :=
    (hγ.continuousOn (z₀, s) ⟨hz₀, has.le, hsc⟩).preimage_mem_nhdsWithin
      (hN.mem_nhds hpN)
  obtain ⟨V, hV, hzV, hVU, l, r, hal, hls, hsr, hrc, hmap, htime⟩ :=
    exists_open_closed_family_neighborhood hU hz₀ has hsc hnear
  have hsub : V ×ˢ Icc l r ⊆ U ×ˢ Icc a c :=
    prod_mono hVU (Icc_subset_Icc hal.le hrc)
  exact ⟨b, V, hV, hzV, hVU, l, r, hal, hls, hsr, hrc, htime, lift ∘ γ,
    hlift.comp (hγ.mono hsub) hmap,
    fun z hz => hright (γ z) (hmap hz), fun z hz => hclock (γ z) (hmap hz)⟩

end PoincareConjecture.M14
