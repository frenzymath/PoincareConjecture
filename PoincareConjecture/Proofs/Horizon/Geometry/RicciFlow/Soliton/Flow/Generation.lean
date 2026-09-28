import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flow.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flow.Regularity.Potential
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flow.Complete.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flow.SelfSimilar.Construction









set_option autoImplicit false
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]



theorem exists_shrinkingSolitonFlow (S : GradientShrinkingSolitonData n M) :
    Nonempty (ShrinkingSolitonFlow S) := by
  have hf := S.potential_contMDiff
  obtain ⟨C, hC, hess⟩ := S.exists_hessian_quadratic_bound
  obtain ⟨Φ, h0, hΦ, hadd, hs⟩ :=
    S.connection.exists_complete_gradientFlow_of_bounded_hessian S.complete hf hC hess
  exact ⟨S.flowOfCompleteGradientFlow hf Φ h0 hadd hs hΦ⟩

end PoincareConjecture
