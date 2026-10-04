import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Interval
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Quantitative axial alignment

The interval estimate supplies the longitudinal component of a neck geodesic.
This file records the scale-independent Hilbert-space conversion from that
component estimate to the ambient tangent estimate used by calibrated fluxes.
-/

set_option autoImplicit false

open Set
open scoped InnerProductSpace

namespace PoincareMT.EpsilonNeck

/- A unit vector whose axial component is close to one is close to the axial
unit vector itself.  This is the final pointwise linear-algebra step in the
neck-geodesic argument. -/
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

/- The preceding conversion is pointwise, so it applies uniformly to a
parameterized minimizing segment once the longitudinal and unit-speed bounds
have been supplied by the neck metric-jet consumer. -/
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

end PoincareMT.EpsilonNeck
