import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.TerminalBlowup.AngularCollapse
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.TerminalBlowup.TipPropagation

/-!
# Pointwise terminal blowup from the independent gradient control

Morgan-Tian Proposition 12.31, pp. 325-326. Angular collapse already
forces scalar divergence at every nonzero point. The independent guarded
gradient bound then propagates that conclusion to the tip. Neither a
uniform scalar lower rate nor the extra-time canonical alternative is
assumed in this implication.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.RepairedStandardCapExistenceData

/-- Proposition 12.31: actual angular collapse together with an
independently established guarded gradient estimate gives scalar divergence
at every fixed point of the selected standard solution. -/
theorem scalar_tendsto_of_guarded_gradient
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀)
    {A H : ℝ} (hA : 0 < A)
    (hgrad : ∀ t ∈ Ico 0 E.flow.base.lifetime, ∀ x : StandardCapSpace,
      H ≤ (E.flow.connection t).scalarCurvature x →
      ∀ v : TangentSpace (𝓡 3) x, (E.flow.metric t).inner x v v = 1 →
        |mvfderiv (𝓡 3) (E.flow.connection t).scalarCurvature x v| ≤
          A * (E.flow.connection t).scalarCurvature x ^ (3 / 2 : ℝ))
    (x : StandardCapSpace) :
    Tendsto (fun t => (E.flow.connection t).scalarCurvature x) (𝓝[<] 1) atTop := by
  by_cases hx : x = 0
  · subst x
    exact E.scalar_tendsto_at_origin_of_tendsto_off_origin P hA hgrad
      (fun y hy => E.scalar_tendsto_off_origin P hy)
  · exact E.scalar_tendsto_off_origin P hx

end PoincareMT.RepairedStandardCapExistenceData
