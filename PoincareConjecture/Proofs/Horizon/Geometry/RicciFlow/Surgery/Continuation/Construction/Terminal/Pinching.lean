import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Extension.TerminalPinching
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Local











set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Surgery.Terminal

variable {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]



theorem terminal_pinched (H : SingularTimeAssumptions G T M)
    (Q : SingularLimitConclusion H) :
    SurgeryPinchedAt (Q.extension.extended.connection T) T := by
  have hT0 : 0 ≤ T := (H.interval_nonnegative H.reference.tMinus_mem).trans
    H.reference.tMinus_lt.le
  have hp (x : (Q.extension.extended.slice T).carrier) :=
    DeepHorn.extension_hamiltonIveyPinchedAt_terminal ricciFlowCurvatureTheory.toCalculus
      H Q.extension ((Q.extension.extended.slice_nonempty_iff T).mp ⟨x⟩)
  exact ⟨hT0, fun x _ => (hp x).2.2.1 x, fun x _ => (hp x).2.2.2 x⟩

end PoincareConjecture.Surgery.Terminal
