import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.CapGeometry.UnitTimeScalarEstimates
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.TerminalBlowup.Pointwise
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.ScalarLowerBound.ScalarFloor
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.ScalarLowerBound.Rate

/-!
# The independent scalar lower rate on the selected flow

Morgan-Tian Proposition 12.31, pp. 325-326. The high-curvature
unit-time canonical theorem gives guarded analytic controls; radial
angular collapse and the gradient estimate give pointwise blowup.
The reciprocal argument then gives the uniform lower rate before the
final extra-time canonical alternative is used.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.RepairedStandardCapExistenceData

/-- Proposition 12.31: pointwise terminal blowup follows independently
from the checked unit-time geometric alternatives and angular collapse. -/
theorem scalar_tendsto_from_unit_time (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (x : StandardCapSpace) :
    Tendsto (fun t => (E.flow.connection t).scalarCurvature x) (𝓝[<] 1) atTop := by
  obtain ⟨A, _H, hA, _hH, hbounds⟩ :=
    M35.OrdinaryRealization.exists_unit_time_scalar_estimates P E
  exact E.scalar_tendsto_of_guarded_gradient P.curvature hA
    (fun t ht y hy => (hbounds t ht y hy).1) x

/-- Proposition 12.31: one positive scalar-rate constant precedes all
points and times, independently of the final extra-time alternative. -/
theorem scalar_lower_rate_from_unit_time (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Ico 0 E.flow.base.lifetime, ∀ x : StandardCapSpace,
      c / (1 - t) ≤ (E.flow.connection t).scalarCurvature x := by
  obtain ⟨A, H, hA, hH, hbounds⟩ :=
    M35.OrdinaryRealization.exists_unit_time_scalar_estimates P E
  obtain ⟨B, hB, hglobal⟩ := E.exists_scalar_floor P.curvature
  apply E.scalar_lower_rate_of_blowup_and_guarded_bound P.curvature
  · intro T hT
    exact ⟨B, hB, fun t ht x => hglobal t ⟨ht.1, ht.2.trans_lt hT.2⟩ x⟩
  · exact E.scalar_tendsto_of_guarded_gradient P.curvature hA
      (fun t ht x hx => (hbounds t ht x hx).1)
  · exact ⟨A, H, hA, hH, fun t ht x hx =>
      (le_abs_self _).trans (hbounds t ht x hx).2⟩

end PoincareMT.RepairedStandardCapExistenceData
