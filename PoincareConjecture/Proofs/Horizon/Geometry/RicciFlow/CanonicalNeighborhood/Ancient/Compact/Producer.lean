import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.Alternatives
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.RoundQuotient

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem compactKappaSolutionAlternatives
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ epsilon₃ : ℝ, 0 < epsilon₃ ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₃ →
        ∃ C₁ : ℝ, 0 < C₁ ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
            [T2Space M] [T3Space M] [SecondCountableTopology M]
            [ConnectedSpace M],
            ∀ K : AncientKappaSolution 3 M,
              IsCompact (Set.univ : Set M) →
              Nonempty (RepairedCanonicalNeighborhoodCertificate K epsilon C₁) := by
  classical
  obtain ⟨epsilon₃, h₃, _, halternatives⟩ :=
    CompactKappa.compact_small_or_strong_doubleCapped_with_cores P
  refine ⟨epsilon₃, h₃, ?_⟩
  intro epsilon hepsilon hε
  obtain ⟨C₁, hC₁, hcases⟩ := halternatives epsilon hepsilon hε
  refine ⟨C₁, hC₁, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K hcompact
  refine ⟨⟨hepsilon, hC₁, ?_⟩⟩
  by_cases hround : IsRoundAncientKappaSolution K
  · have hsectional := compactRound_sectionalCurvature (hround 0 le_rfl)
    obtain ⟨Q⟩ := compactRoundAncientQuotient K hcompact hsectional
    exact ⟨.round hsectional Q⟩
  · rcases hcases K hround hcompact with hsmall | hdouble
    · obtain ⟨small⟩ := hsmall
      exact ⟨.compactSmall small⟩
    · obtain ⟨A, B, _, _, _, _, S, _, _, _⟩ := hdouble
      exact ⟨.doubleCapped S⟩

end PoincareConjecture
