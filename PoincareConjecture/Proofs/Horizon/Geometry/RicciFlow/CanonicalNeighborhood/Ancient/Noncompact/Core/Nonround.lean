import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.TimeShift









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

theorem AncientKappaSolution.not_isRound_of_noncompact
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution 3 M) (hnoncompact : ¬ IsCompact (Set.univ : Set M)) :
    ¬ IsRoundAncientKappaSolution K := by
  intro hround
  exact hnoncompact (isCompact_univ_iff.mpr
    (AncientKappaRoundness.compactSpace_of_isRoundMetricSlice (K.flow.connection 0)
      (K.complete 0 le_rfl) (hround 0 le_rfl)))

end PoincareConjecture
