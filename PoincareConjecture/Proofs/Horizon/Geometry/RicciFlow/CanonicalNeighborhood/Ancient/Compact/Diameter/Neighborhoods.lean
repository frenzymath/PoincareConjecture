import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Contradiction.Sequence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Contradiction.LiftedLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Trichotomy
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Producer
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Cap.Construction












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace RicciFlow.uliftChartedSpace RicciFlow.uliftIsManifold
  AncientKappaSolution.uliftSecondCountable AncientKappaSolution.uliftConnectedSpace



theorem compact_large_diameter_neighborhoods
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 400 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ∀ kappa : ℝ, 0 < kappa →
          ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
            ∀ {M : Type u} [TopologicalSpace M]
              [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
              [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
              [SecondCountableTopology M] [ConnectedSpace M]
              (K : AncientKappaSolution 3 M) (p : M),
              AncientKappaNoncollapsed K.flow kappa → IsCompact (univ : Set M) →
              NoEmbeddedTrivialNormalProjectivePlane K →
              D < Real.sqrt ((K.flow.connection 0).scalarCurvature p) *
                metricDiameter (K.flow.metric 0) univ →
              (∃ N : StrongEvolvingNeck K 0 epsilon, N.center = p) ∨
              (∃ A : CapCertificate (K.flow.metric 0),
                A.epsilon = epsilon ∧ A.cap_constant ≤ C ∧ p ∈ A.core) := by
  classical
  obtain ⟨epsilonL, hL, hsmall, hlimit⟩ :=
    exists_noncompact_lifted_limit_without_models P
  obtain ⟨epsilonP, hP, hpositive⟩ :=
    NoncompactKappa.Positive.uniform_caps_of_core P (noncompactKappaUniformCoreEstimates P)
  refine ⟨min epsilonL epsilonP, lt_min hL hP,
    (min_le_left _ _).trans hsmall, ?_⟩
  intro epsilon hepsilon hε kappa hkappa
  obtain ⟨C₀, hC₀, hcaps⟩ :=
    hpositive epsilon hepsilon (hε.trans (min_le_right _ _))
  obtain ⟨C, hC, hbadlimit⟩ :=
    hlimit epsilon hepsilon (hε.trans (min_le_left _ _)) kappa hkappa C₀ hC₀
  suffices h : ∃ D : ℝ, 0 < D ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        AncientKappaNoncollapsed K.flow kappa → IsCompact (univ : Set M) →
        NoEmbeddedTrivialNormalProjectivePlane K →
        D < Real.sqrt ((K.flow.connection 0).scalarCurvature p) *
          metricDiameter (K.flow.metric 0) univ →
        (∃ N : StrongEvolvingNeck K 0 epsilon, N.center = p) ∨
        (∃ A : CapCertificate (K.flow.metric 0),
          A.epsilon = epsilon ∧ A.cap_constant ≤ C ∧ p ∈ A.core) by
    obtain ⟨D, hD, h⟩ := h
    exact ⟨C, D, hC, hD, h⟩
  by_contra hbad
  obtain ⟨S, _, hno, hdiam, hneck, hcap⟩ :=
    exists_normalized_bad_neighborhood_sequence P hkappa hbad
  obtain ⟨G, _, hnoncompact, _, hnoneck, hnocap, hsphere, hprojective, htwisted⟩ :=
    hbadlimit S hno hdiam hneck hcap
  let L : AncientKappaSolution 3 (ULift.{u} G.limit.carrier.carrier) := G.limit.flow.ulift
  have hpos : M27PositiveSectionalCurvature L 0 := by
    rcases ancientKappaCurvatureTrichotomy P L with hpos | hS | hP | hT
    · exact hpos 0 le_rfl
    · exact (hsphere hS).elim
    · exact (hprojective hP).elim
    · exact (htwisted hT).elim
  obtain ⟨A, hA, hAC, _, hcover⟩ := hcaps L hnoncompact hpos
  by_cases hx : ULift.up G.limit.base ∈ A.core
  · exact hnocap ⟨A, hA, hAC.le, hx⟩
  · exact hnoneck (hcover _ hx)

end PoincareConjecture
