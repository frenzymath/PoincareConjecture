import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Analysis.Coordinates.WithinJetExtraction
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Analysis.Coordinates.WithinJetLimits

/-!
# Smooth compactness on convex relative domains

Countably many families with local eventual bounds on every actual within
jet admit one strict subsequence with smooth limits and uniform convergence
of those jets on compact subsets, including the domain boundary. This is
the analytic endpoint producer for Morgan--Tian Proposition 5.14,
pp. 90-91, and Claim 10.11, p. 255; see task derivation 09.
-/

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

/-- Local eventual within-jet bounds on countably many convex relative
domains produce actual smooth limits and all compact jet tests along one
strict subsequence. The conclusion includes time endpoints whenever the
domain includes them (task derivation 09). -/
theorem exists_common_contDiffOn_subsequence_of_withinJet_bounds
    {E F : ℕ → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    [∀ i, FiniteDimensional ℝ (F i)]
    (S : ∀ i, Set (E i)) [∀ i, LocallyCompactSpace (S i)]
    (hconv : ∀ i, Convex ℝ (S i)) (hS : ∀ i, UniqueDiffOn ℝ (S i))
    (f : ∀ i, ℕ → E i → F i) (hf : ∀ i j, ContDiffOn ℝ ∞ (f i j) (S i))
    (hbound : ∀ i K, IsCompact K → K ⊆ S i → ∀ m : ℕ,
      ∃ B : ℝ, ∀ᶠ j in atTop, ∀ x ∈ K,
        ‖iteratedFDerivWithin ℝ m (f i j) (S i) x‖ ≤ B) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ G : ∀ i, E i → F i,
      (∀ i, ContDiffOn ℝ ∞ (G i) (S i)) ∧
      ∀ i m K, IsCompact K → K ⊆ S i → TendstoUniformlyOn
        (fun j => iteratedFDerivWithin ℝ m (f i (σ j)) (S i))
        (iteratedFDerivWithin ℝ m (G i) (S i)) atTop K := by
  obtain ⟨σ, hσ, g, hg⟩ :=
    exists_common_locallyUniform_withinJet_limits S hconv hS f hf hbound
  have hlimit (i : ℕ) := exists_contDiffOn_of_locallyUniform_withinJet_limits
    (hconv i) (hS i) (fun j => f i (σ j)) (fun j => hf i (σ j)) (g i) (hg i)
  choose G hG hjets using hlimit
  refine ⟨σ, hσ, G, hG, fun i m K hK hKS => ?_⟩
  exact ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    ((hg i m).mono hKS)).congr_right ((hjets i m).symm.mono hKS)
