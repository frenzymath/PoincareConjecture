import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Extension.TerminalPinching
import PoincareLib.Geometry.RicciFlow.Curvature.Construction
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Local

/-!
# Surgery pinching of the singular terminal metric

The constructed curvature calculus and terminal Hamilton--Ivey theorem
give the exact metric-surgery pinching inequalities. An empty terminal
slice satisfies the spatial conditions without requiring an included
terminal time.

Source: Morgan--Tian, Claim 11.32, pp. 287-288.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.Surgery.Terminal

variable {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]

/-- Every singular terminal metric satisfies the original surgery pinching
inequalities, including the possibility of an empty terminal slice. -/
theorem terminal_pinched (H : SingularTimeAssumptions G T M)
    (Q : SingularLimitConclusion H) :
    SurgeryPinchedAt (Q.extension.extended.connection T) T := by
  have hT0 : 0 ≤ T := (H.interval_nonnegative H.reference.tMinus_mem).trans
    H.reference.tMinus_lt.le
  have hp (x : (Q.extension.extended.slice T).carrier) :=
    DeepHorn.extension_hamiltonIveyPinchedAt_terminal ricciFlowCurvatureTheory.toCalculus
      H Q.extension ((Q.extension.extended.slice_nonempty_iff T).mp ⟨x⟩)
  exact ⟨hT0, fun x _ => (hp x).2.2.1 x, fun x _ => (hp x).2.2.2 x⟩

end PoincareMT.Surgery.Terminal
