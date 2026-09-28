import PoincareConjecture.Proofs.M35.TerminalBlowup.AngularCollapse
import PoincareConjecture.Proofs.M35.TerminalBlowup.TipPropagation











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RepairedStandardCapExistenceData




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

end PoincareConjecture.RepairedStandardCapExistenceData
