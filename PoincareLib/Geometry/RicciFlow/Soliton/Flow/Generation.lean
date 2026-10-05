import PoincareLib.Geometry.RicciFlow.Soliton.Flow.Bounds
import PoincareLib.Geometry.RicciFlow.Soliton.Flow.Regularity.Potential
import PoincareLib.Geometry.RicciFlow.Soliton.Flow.Complete.Gradient
import PoincareLib.Geometry.RicciFlow.Soliton.Flow.SelfSimilar.Construction

/-! # Shrinking solitons generate normalized ancient Ricci flows

Morgan--Tian, Chapter 3, Section 2; Definition 9.41 and Theorem 9.42,
pp. 206-208. The C2 potential is bootstrapped to smoothness. Its bounded
Hessian confines gradient trajectories in compact metric balls for finite
times, producing a complete smooth gradient action. The time change
`-log (-t)` and rescaling `-t` give the normalized self-similar Ricci flow.
-/

set_option autoImplicit false
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-- The exact frozen soliton hypotheses produce a smooth normalized ancient
flow, without any additional regularity or self-similarity assumption. -/
theorem exists_shrinkingSolitonFlow (S : GradientShrinkingSolitonData n M) :
    Nonempty (ShrinkingSolitonFlow S) := by
  have hf := S.potential_contMDiff
  obtain ⟨C, hC, hess⟩ := S.exists_hessian_quadratic_bound
  obtain ⟨Φ, h0, hΦ, hadd, hs⟩ :=
    S.connection.exists_complete_gradientFlow_of_bounded_hessian S.complete hf hC hess
  exact ⟨S.flowOfCompleteGradientFlow hf Φ h0 hadd hs hΦ⟩

end PoincareMT
