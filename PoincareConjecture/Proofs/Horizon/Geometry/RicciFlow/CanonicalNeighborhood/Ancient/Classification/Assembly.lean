import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Constants
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Round
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Pointwise.Round
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Normalization.Pointwise
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.ScalarDerivatives.Main
import PoincareConjecture.Statements.M27KappaAlternatives
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Trichotomy
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Models
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Twisted.Alternatives

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem m27KappaAlternatives_of_nonround_geometry
    (P : M27KappaAlternativePredecessors.{u})
    (hclassification : ∃ epsilonBar : ℝ, 0 < epsilonBar ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilonBar →
        ∃ C : ℝ, 0 < C ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
            [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
            ∀ K : AncientKappaSolution 3 M, ¬ IsRoundAncientKappaSolution K →
              M27KappaNine93Conclusion K epsilon C)
    (hpointwise : ∃ epsilonPrime : ℝ, 0 < epsilonPrime ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilonPrime →
        ∃ C : ℝ, 0 < C ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
            [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
            ∀ K : AncientKappaSolution 3 M, ¬ IsRoundAncientKappaSolution K →
              ¬ Nonempty (M27ProjectivePlaneLineFlowCertificate K) →
                ∀ t, t ≤ 0 → ∀ x : M,
                  M27StrongCanonicalNeighborhood K t x epsilon C) :
    RepairedKappaAlternativeTheory.{u} := by
  classical
  obtain ⟨Cd, hCd, hderiv⟩ := uniformKappaScalarDerivativeBounds P
  constructor
  · obtain ⟨epsilonBar, hbar, hgeom⟩ := hclassification
    refine ⟨epsilonBar, hbar, fun epsilon hepsilon hsmall => ?_⟩
    obtain ⟨Cg, hCg, hgeom⟩ := hgeom epsilon hepsilon hsmall
    refine ⟨max Cg Cd, lt_of_lt_of_le hCg (le_max_left _ _), ?_⟩
    intro M _ _ _ _ _ _ _ _ _ K
    have hd : M27ScalarDerivativeBounds K Cd := hderiv K
    refine ⟨hepsilon, lt_of_lt_of_le hCg (le_max_left _ _), ?_,
      hd.horizon_mono_constant (le_max_right _ _)⟩
    by_cases hr : IsRoundAncientKappaSolution K
    · obtain ⟨Q⟩ := roundAncientSphericalSpaceForm K hr
      exact .round hr Q
    · obtain ⟨B, _, _, hb⟩ := hd
      exact (hgeom K hr).mono_constant hCg (le_max_left _ _) (fun x => (hb 0 le_rfl x).1)
  · obtain ⟨epsilonPrime, hprime, hpoint⟩ := hpointwise
    refine ⟨epsilonPrime, hprime, fun epsilon hepsilon hsmall => ?_⟩
    obtain ⟨C, hC, hpoint⟩ := hpoint epsilon hepsilon hsmall
    refine ⟨C, hC, ?_⟩
    intro M _ _ _ _ _ _ _ _ _ K hexception t ht x
    by_cases hr : IsRoundAncientKappaSolution K
    · exact strongCanonicalNeighborhood_of_round K hr hepsilon C t ht x
    · exact hpoint K hr hexception t ht x

theorem m27KappaAlternatives_of_nonround_classification
    (P : M27KappaAlternativePredecessors.{u})
    (hclassification : ∃ epsilonBar : ℝ, 0 < epsilonBar ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilonBar →
        ∃ C : ℝ, 0 < C ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
            [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
            ∀ K : AncientKappaSolution 3 M, ¬ IsRoundAncientKappaSolution K →
              M27KappaNine93Conclusion K epsilon C) :
    RepairedKappaAlternativeTheory.{u} := by
  apply m27KappaAlternatives_of_nonround_geometry P hclassification
  obtain ⟨epsilonBar, hbar, hgeom⟩ := hclassification
  refine ⟨epsilonBar / 2, by positivity, fun epsilon hepsilon hsmall => ?_⟩
  obtain ⟨C, hC, hgeom⟩ := hgeom epsilon hepsilon (by linarith)
  refine ⟨canonicalComponentConstant C, ?_, ?_⟩
  · have hpow := Real.rpow_pos_of_pos hC (1 / 2 : ℝ)
    dsimp [canonicalComponentConstant]
    positivity
  · intro M _ _ _ _ _ _ _ _ _ K _ hexception t ht x
    apply strongCanonicalNeighborhoods_of_uniform_classification P hepsilon hC
      (fun L => ?_) K hexception t ht x
    by_cases hr : IsRoundAncientKappaSolution L
    · obtain ⟨Q⟩ := roundAncientSphericalSpaceForm L hr
      exact .round hr Q
    · exact hgeom L hr

theorem m27KappaAlternatives_of_positive_classification
    (P : M27KappaAlternativePredecessors.{u})
    (hclassification : ∃ epsilonBar : ℝ, 0 < epsilonBar ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilonBar →
        ∃ C : ℝ, 0 < C ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
            [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
            ∀ K : AncientKappaSolution 3 M, ¬ IsRoundAncientKappaSolution K →
              (∀ t : ℝ, t ≤ 0 → M27PositiveSectionalCurvature K t) →
                M27KappaNine93Conclusion K epsilon C) :
    RepairedKappaAlternativeTheory.{u} := by
  obtain ⟨ep, hep, hpositive⟩ := hclassification
  obtain ⟨es, hes, _, hsphere⟩ := m27SphereLineAlternatives P
  obtain ⟨eq, heq, _, hquotient⟩ := m27TwistedAlternatives P
  obtain ⟨_, _, hderiv⟩ := uniformKappaScalarDerivativeBounds P
  apply m27KappaAlternatives_of_nonround_classification P
  refine ⟨min ep (min es eq), lt_min hep (lt_min hes heq), ?_⟩
  intro epsilon hepsilon hsmall
  have hp := hsmall.trans_le (min_le_left ep (min es eq))
  have hs := hsmall.le.trans ((min_le_right ep (min es eq)).trans (min_le_left es eq))
  have hq := hsmall.le.trans ((min_le_right ep (min es eq)).trans (min_le_right es eq))
  obtain ⟨Cp, hCp, hpositive⟩ := hpositive epsilon hepsilon hp
  obtain ⟨Cq, hCq, hquotient⟩ := hquotient epsilon hepsilon hq
  refine ⟨max Cp Cq, hCp.trans_le (le_max_left _ _), ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K hnonround
  obtain ⟨_, _, _, hscalar⟩ := hderiv K
  rcases P.classificationServices.curvatureTrichotomy K with
    hpos | hmodel | hmodel | hmodel
  · exact (hpositive K hnonround hpos).mono_constant hCp (le_max_left _ _)
      (fun x => (hscalar 0 le_rfl x).1)
  · obtain ⟨model⟩ := hmodel
    exact hsphere epsilon hepsilon hs K model (max Cp Cq)
  · obtain ⟨model⟩ := hmodel
    exact .projectivePlaneLine model
  · obtain ⟨model⟩ := hmodel
    exact (hquotient K model).mono_constant hCq (le_max_right _ _)
      (fun x => (hscalar 0 le_rfl x).1)

end PoincareConjecture
