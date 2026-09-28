import PoincareConjecture.Proofs.M35.CapGeometry.UnitTimeScalarEstimates
import PoincareConjecture.Proofs.M35.TerminalBlowup.Pointwise
import PoincareConjecture.Proofs.M35.Prop12_31.ScalarFloor
import PoincareConjecture.Proofs.M35.Prop12_31_ScalarRate











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RepairedStandardCapExistenceData



theorem scalar_tendsto_from_unit_time (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (x : StandardCapSpace) :
    Tendsto (fun t => (E.flow.connection t).scalarCurvature x) (𝓝[<] 1) atTop := by
  obtain ⟨A, _H, hA, _hH, hbounds⟩ :=
    M35.OrdinaryRealization.exists_unit_time_scalar_estimates P E
  exact E.scalar_tendsto_of_guarded_gradient P.curvature hA
    (fun t ht y hy => (hbounds t ht y hy).1) x



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

end PoincareConjecture.RepairedStandardCapExistenceData
