import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.MinimumBarrier
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Attainment

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.AncientKappaSolution

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem exists_reducedLength_minimizer_le_one (K : AncientKappaSolution 2 M)
    (p : M) {τ : ℝ} (hτ : 0 < τ) :
    ∃ q : M, (∀ y : M, reducedLength K.flow 0 p q τ ≤ reducedLength K.flow 0 p y τ) ∧
      reducedLength K.flow 0 p q τ ≤ 1 := by
  obtain ⟨q, hq⟩ := K.exists_reducedLength_eq_spatialInfimum p hτ
  exact ⟨q, fun y ↦ hq.trans_le (K.spatialReducedLengthInfimum_le p y τ),
    hq.trans_le (K.spatialReducedLengthInfimum_le_one p hτ)⟩

end PoincareConjecture.AncientKappaSolution
