import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.CompactStageRegularity











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.RegularPointedMetricConvergence

variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, T2Space (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)]
  {g : ∀ k, RiemannianMetric 3 (M k)} {p : ∀ k, M k}




theorem exists_eventually_regular_path_capture
    (G : RegularPointedMetricConvergence g p) :
    letI := G.limitCarrier.topologicalSpace
    ∀ (j : ℕ) (delta : ℝ), 0 < delta →
      ∃ ell : ℕ, ∀ᶠ k in atTop, ell ≤ k ∧
        ∀ (gamma : ℝ → M (G.subsequence k)) (a b : ℝ), a ≤ b →
          ContinuousOn gamma (Icc a b) →
          MapsTo gamma (Icc a b) (regularPoints (g (G.subsequence k)) delta) →
          gamma a ∈ G.embedding k '' G.exhaustion j →
          MapsTo gamma (Icc a b) (G.embedding k '' G.exhaustion ell) := by
  let := G.limitCarrier.topologicalSpace
  intro j delta hdelta
  obtain ⟨rho, hrho, hstage⟩ := G.exists_eventual_compact_stage_regularComponent j
  let eta := min delta rho
  have heta : 0 < eta := lt_min hdelta hrho
  obtain ⟨ell, hcoverage⟩ := G.regular_component_coverage eta heta
  refine ⟨ell, ?_⟩
  filter_upwards [hstage, hcoverage] with k hkstage hkcover
  refine ⟨hkcover.1, ?_⟩
  intro gamma a b hab hgamma hregular hstart
  obtain ⟨x, hx, hxstart⟩ := hstart
  have hanchor : gamma a ∈ regularComponent
      (g (G.subsequence k)) (p (G.subsequence k)) eta :=
    regularComponent_antitone _ _ (min_le_right _ _)
      (hkstage ⟨x, subset_closure hx, hxstart⟩)
  have hreg : gamma '' Icc a b ⊆ regularPoints (g (G.subsequence k)) eta := by
    rintro _ ⟨t, ht, rfl⟩
    exact regularPoints_antitone _ (min_le_left _ _) (hregular ht)
  have hconn := isPreconnected_Icc.image gamma hgamma
  have hcomp : gamma '' Icc a b ⊆ regularComponent
      (g (G.subsequence k)) (p (G.subsequence k)) eta := by
    change gamma '' Icc a b ⊆ connectedComponentIn _ _
    rw [connectedComponentIn_eq hanchor]
    exact hconn.subset_connectedComponentIn
      (mem_image_of_mem gamma (left_mem_Icc.mpr hab)) hreg
  intro t ht
  exact hkcover.2 (hcomp (mem_image_of_mem gamma ht))

end PoincareConjecture.M28.RegularPointedMetricConvergence
