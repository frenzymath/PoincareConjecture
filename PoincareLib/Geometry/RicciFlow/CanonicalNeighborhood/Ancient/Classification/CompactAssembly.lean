import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Assembly
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Producer

/-!
# M27 assembly from compact classification

The shared-service positive noncompact producer supplies its original cap,
Euclidean coordinates, and cap-core-or-strong-neck coverage. The trichotomy
assembly handles the three null-curvature models and the round branch.
Only compact positive nonround classification remains in this reduction.

Reference: Morgan--Tian, Theorem 9.93 and Corollary 9.94, pp. 242--243.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- The checked noncompact producer reduces the full unchanged M27 theory
to uniform classification of compact positive nonround solutions. -/
theorem m27KappaAlternatives_of_compact_classification
    (P : M27KappaAlternativePredecessors.{u})
    (hcompact : ∃ epsilonBar : ℝ, 0 < epsilonBar ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilonBar →
        ∃ C : ℝ, 0 < C ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
            [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
            ∀ K : AncientKappaSolution 3 M, ¬ IsRoundAncientKappaSolution K →
              IsCompact (Set.univ : Set M) →
              (∀ t : ℝ, t ≤ 0 → M27PositiveSectionalCurvature K t) →
                M27KappaNine93Conclusion K epsilon C) :
    RepairedKappaAlternativeTheory.{u} := by
  classical
  obtain ⟨ec, hec, hcompact⟩ := hcompact
  obtain ⟨en, hen, hnoncompact⟩ := positiveCurvatureCappedEuclidean_of_m27 P
  obtain ⟨_, _, hderiv⟩ := uniformKappaScalarDerivativeBounds P
  apply m27KappaAlternatives_of_positive_classification P
  refine ⟨min ec en, lt_min hec hen, ?_⟩
  intro epsilon hepsilon hsmall
  obtain ⟨Cc, hCc, hcompact⟩ :=
    hcompact epsilon hepsilon (hsmall.le.trans (min_le_left _ _))
  obtain ⟨Cn, hCn, hnoncompact⟩ :=
    hnoncompact epsilon hepsilon (hsmall.le.trans (min_le_right _ _))
  refine ⟨max Cc Cn, hCc.trans_le (le_max_left _ _), ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K hnonround hpositive
  obtain ⟨_, _, _, hscalar⟩ := hderiv K
  by_cases hc : IsCompact (Set.univ : Set M)
  · exact (hcompact K hnonround hc hpositive).mono_constant hCc (le_max_left _ _)
      (fun x => (hscalar 0 le_rfl x).1)
  · exact (hnoncompact K hc (hpositive 0 le_rfl)).mono_constant hCn (le_max_right _ _)
      (fun x => (hscalar 0 le_rfl x).1)

end PoincareMT
