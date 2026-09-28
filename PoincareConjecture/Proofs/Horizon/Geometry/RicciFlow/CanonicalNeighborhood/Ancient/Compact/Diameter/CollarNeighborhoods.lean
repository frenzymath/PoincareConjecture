import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Contradiction.FineNeighborhoods

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.CompactKappa

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace RicciFlow.uliftChartedSpace RicciFlow.uliftIsManifold
  AncientKappaSolution.uliftSecondCountable AncientKappaSolution.uliftConnectedSpace

theorem compact_large_diameter_strong_collar_neighborhoods
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
              HasStrongCollarCap K epsilon C p := by
  classical
  obtain ⟨epsilonL, hL, hsmall, hlimit⟩ :=
    exists_noncompact_limit_without_strong_collars P
  obtain ⟨epsilonN, hN, _, hneighborhoods⟩ := uniform_noncompact_fine_neighborhoods P
  refine ⟨min epsilonL epsilonN, lt_min hL hN,
    (min_le_left _ _).trans hsmall, ?_⟩
  intro epsilon hepsilon hε kappa hkappa
  obtain ⟨C₀, hC₀, hnoncompact⟩ :=
    hneighborhoods epsilon hepsilon (hε.trans (min_le_right _ _))
  obtain ⟨C, hC, hbadlimit⟩ := hlimit kappa hkappa C₀ hC₀
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
        HasStrongCollarCap K epsilon C p by
    obtain ⟨D, hD, h⟩ := h
    exact ⟨C, D, hC, hD, h⟩
  by_contra hbad
  obtain ⟨S, _, hno, hdiam, hneck, hcap⟩ :=
    exists_normalized_bad_neighborhood_sequence_strong_collars P hkappa hbad
  obtain ⟨G, _, hnoncompactG, hnoG, hnoneck, hnocap⟩ :=
    hbadlimit epsilon hepsilon (hε.trans (min_le_left _ _)) S hno hdiam hneck hcap
  let L : AncientKappaSolution 3 (ULift.{u} G.limit.carrier.carrier) := G.limit.flow.ulift
  have hnoncompactL : ¬ IsCompact (univ : Set (ULift.{u} G.limit.carrier.carrier)) := by
    intro hcompact
    apply hnoncompactG
    simpa only [image_univ, EquivLike.range_eq_univ] using
      hcompact.image (Homeomorph.ulift : ULift.{u} G.limit.carrier.carrier ≃ₜ
        G.limit.carrier.carrier).continuous
  have hnoL : NoEmbeddedTrivialNormalProjectivePlane L :=
    G.limit.flow.noEmbeddedTrivialNormalProjectivePlane_ulift hnoG
  rcases hnoncompact L hnoncompactL hnoL (ULift.up G.limit.base) with ⟨N, hN⟩ | hA
  · exact hnoneck ⟨G.limit.flow.strongNeckFromUlift N, by simp [hN]⟩
  · exact hnocap hA.of_ulift

end PoincareConjecture.CompactKappa
