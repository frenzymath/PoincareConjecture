import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Producer
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Cap.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.End.Attachment
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Positive.Attachment

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem positiveCurvatureStrongCappedTubes_of_services
    (P : NoncompactKappaServices.{u}) :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilonStar →
        ∃ C : ℝ, 0 < C ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
            [T2Space M] [T3Space M] [SecondCountableTopology M]
            [ConnectedSpace M],
            ∀ K : AncientKappaSolution 3 M,
              ¬ IsCompact (Set.univ : Set M) →
              M27PositiveSectionalCurvature K 0 →
              ∃ T : M26StrongCappedTube K 0 epsilon C,
                ∀ x : M, x ∈ T.cap.cap.core ∨
                  ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x := by
  obtain ⟨epsilonCap, hcap, hcaps⟩ :=
    NoncompactKappa.Positive.uniform_caps_of_core_of_services P
      (noncompactKappaUniformCoreEstimates_of_services P)
  obtain ⟨epsilonTube, htube, _, htubes⟩ :=
    NoncompactKappa.Positive.exists_strongCappedTube_preserving_cap_threshold.{u}
  refine ⟨min epsilonCap epsilonTube, lt_min hcap htube, ?_⟩
  intro epsilon hepsilon hest
  obtain ⟨C, hC, hconstructed⟩ :=
    hcaps epsilon hepsilon (hest.trans (min_le_left _ _))
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K hnoncompact hpositive
  obtain ⟨cap, he, hconstant, _, hstrong⟩ := hconstructed K hnoncompact hpositive
  obtain ⟨T, _, _, hcoverage⟩ :=
    htubes K cap he hconstant.le (hest.trans (min_le_right _ _)) hstrong
  exact ⟨T, hcoverage⟩

theorem positiveCurvatureStrongCappedTubes
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilonStar →
        ∃ C : ℝ, 0 < C ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
            [T2Space M] [T3Space M] [SecondCountableTopology M]
            [ConnectedSpace M],
            ∀ K : AncientKappaSolution 3 M,
              ¬ IsCompact (Set.univ : Set M) →
              M27PositiveSectionalCurvature K 0 →
              Nonempty (M26StrongCappedTube K 0 epsilon C) := by
  obtain ⟨epsilonStar, hstar, hmake⟩ :=
    positiveCurvatureStrongCappedTubes_of_services P.noncompactServices
  refine ⟨epsilonStar, hstar, ?_⟩
  intro epsilon hepsilon hest
  obtain ⟨C, hC, hconstructed⟩ := hmake epsilon hepsilon hest
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K hnoncompact hpositive
  obtain ⟨T, _⟩ := hconstructed K hnoncompact hpositive
  exact ⟨T⟩

theorem positiveCurvatureCappedEuclidean_of_m27
    (P : M27KappaAlternativePredecessors.{u}) :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilonStar →
        ∃ C : ℝ, 0 < C ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
            [T2Space M] [T3Space M] [SecondCountableTopology M]
            [ConnectedSpace M],
            ∀ K : AncientKappaSolution 3 M,
              ¬ IsCompact (Set.univ : Set M) →
              M27PositiveSectionalCurvature K 0 →
              M27KappaNine93Conclusion K epsilon C := by
  obtain ⟨epsilonCap, hcap, hcaps⟩ :=
    NoncompactKappa.Positive.uniform_caps_of_core_of_services P.noncompactServices
      (noncompactKappaUniformCoreEstimates_of_services P.noncompactServices)
  obtain ⟨epsilonTube, htube, _, htubes⟩ :=
    NoncompactKappa.Positive.exists_coveredCappedTube_of_cap_threshold.{u}
  refine ⟨min epsilonCap epsilonTube, lt_min hcap htube, ?_⟩
  intro epsilon hepsilon hest
  obtain ⟨C, hC, hconstructed⟩ :=
    hcaps epsilon hepsilon (hest.trans (min_le_left _ _))
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K hnoncompact hpositive
  obtain ⟨cap, he, hconstant, _, hstrong⟩ := hconstructed K hnoncompact hpositive
  obtain ⟨A, hAcap, hAepsilon, hwhole, hdisjoint⟩ :=
    htubes K cap he hconstant.le (hest.trans (min_le_right _ _)) hstrong
  exact m27CappedEuclidean_of_covered_attachment K hnoncompact hpositive A
    (hAcap ▸ he) hAepsilon (hAcap ▸ hconstant.le) hwhole
    (hAcap ▸ hdisjoint) (hAcap ▸ hstrong)

end PoincareConjecture
