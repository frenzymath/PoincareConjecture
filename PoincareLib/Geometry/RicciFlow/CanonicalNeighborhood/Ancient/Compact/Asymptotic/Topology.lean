import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Asymptotic.Cover
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Topology.Closed

/-!
# Closed topology from the actual large past slices

The normalized past slice has a whole neck/cap cover and cannot be round or
covered by two controlled caps. The frozen topology service therefore gives
a closed smooth model and an actual whole static double-capped tube on that
same carrier. Its static tube does not yet assert evolving-neck coverage.

Reference: Morgan--Tian, Theorem 9.89, pp. 240--241 (`MT2007`).
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- The earlier-slice construction retains the original carrier's closed
model and the entire static double-capped geometry with uniform constants. -/
theorem compact_nonround_exists_earlier_doubleCapped_normalization
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 400 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ∃ C : ℝ, 0 < C ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
            [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
            [SecondCountableTopology M] [ConnectedSpace M]
            (K : AncientKappaSolution 3 M),
            IsCompact (univ : Set M) → ¬ IsRoundAncientKappaSolution K →
            NoEmbeddedTrivialNormalProjectivePlane K → ∀ b : ℝ,
            ∃ t : ℝ, t < min b 0 ∧ ∃ p : M,
              ∃ A : AncientKappaNormalization K p t,
                ∃ kind : ClosedComponentKind,
                  Nonempty (ClosedComponentCertificate kind (univ : Set M)) ∧
                  ∃ T : DoubleCappedTubeCertificate (A.target.flow.metric 0),
                    T.carrier = univ ∧ T.cap₁.epsilon = epsilon ∧
                    T.cap₂.epsilon = epsilon ∧ T.tube.epsilon = epsilon ∧
                    T.cap₁.cap_constant ≤ C ∧ T.cap₂.cap_constant ≤ C := by
  obtain ⟨epsilonA, hA, hsmall, hpast⟩ :=
    compact_nonround_exists_earlier_covered_normalization P
  obtain ⟨epsilonG, hG, _, hglobal⟩ := compact_closed_shape_of_neighborhoods P
  refine ⟨min epsilonA epsilonG, lt_min hA hG,
    (min_le_left _ _).trans hsmall, ?_⟩
  intro epsilon hepsilon hε
  obtain ⟨C, hC, hconstructed⟩ := hpast epsilon hepsilon (hε.trans (min_le_left _ _))
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K hcompact hnonround hno b
  obtain ⟨t, ht, p, A, _, htwo, hcover⟩ := hconstructed K hcompact hnonround hno b
  obtain ⟨kind, model, ⟨shape⟩⟩ := hglobal A.target hepsilon
    (hε.trans (min_le_right _ _)) hC hcompact hcover
  exact ⟨t, ht, p, A, kind, model, shape.doubleCapped_of_not_twoCaps htwo⟩

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

/-- The smooth closed model obtained in the distant past is on the original
compact carrier, so it also describes its terminal slice. -/
theorem compact_nonround_closed_model
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    (K : AncientKappaSolution 3 M) (hcompact : IsCompact (univ : Set M))
    (hnonround : ¬ IsRoundAncientKappaSolution K)
    (hno : NoEmbeddedTrivialNormalProjectivePlane K) :
    ∃ kind : ClosedComponentKind,
      Nonempty (ClosedComponentCertificate kind (univ : Set M)) := by
  obtain ⟨epsilon₀, hε₀, _, hfamily⟩ :=
    compact_nonround_exists_earlier_doubleCapped_normalization P
  obtain ⟨_, _, hconstructed⟩ := hfamily epsilon₀ hε₀ le_rfl
  obtain ⟨_, _, _, _, kind, model, _⟩ := hconstructed K hcompact hnonround hno 0
  exact ⟨kind, model⟩

end PoincareMT
