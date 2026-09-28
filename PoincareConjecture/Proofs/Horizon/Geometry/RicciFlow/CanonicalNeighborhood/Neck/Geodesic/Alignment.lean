import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Interval
import Mathlib.Analysis.InnerProductSpace.Basic

set_option autoImplicit false

open Set
open scoped InnerProductSpace

namespace PoincareConjecture.EpsilonNeck

theorem norm_sub_le_of_unit_inner_ge
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u e : E} {α : ℝ}
    (hu : ‖u‖ = 1) (he : ‖e‖ = 1) (hα : 0 ≤ α)
    (hinner : 1 - α ^ 2 / 2 ≤ ⟪u, e⟫_ℝ) :
    ‖u - e‖ ≤ α := by
  have hsq := norm_sub_sq_real u e
  rw [hu, he] at hsq
  have hsq' : ‖u - e‖ ^ 2 ≤ α ^ 2 := by
    nlinarith [hinner]
  exact (sq_le_sq₀ (norm_nonneg _) hα).mp hsq'

theorem norm_sub_le_of_scaled_velocity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u e : E} {v r α : ℝ}
    (hu : ‖u‖ = 1) (he : ‖e‖ = 1) (hα : 0 ≤ α)
    (hinner_eq : ⟪u, e⟫_ℝ = r * v)
    (hlower : 1 - α ^ 2 / 2 ≤ r * v) :
    ‖u - e‖ ≤ α := by
  apply norm_sub_le_of_unit_inner_ge hu he hα
  rw [hinner_eq]
  exact hlower

end PoincareConjecture.EpsilonNeck
