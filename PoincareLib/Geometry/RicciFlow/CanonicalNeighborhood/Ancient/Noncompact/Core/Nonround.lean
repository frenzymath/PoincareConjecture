import PoincareLib.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.TimeShift

/-!
# Noncompact ancient solutions are nonround

A complete positive round slice is compact by Bonnet--Myers. Thus a noncompact
ancient solution lies in the universally noncollapsed branch used in
Morgan--Tian, Proposition 9.85(1), pp. 237--239.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT

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

end PoincareMT
