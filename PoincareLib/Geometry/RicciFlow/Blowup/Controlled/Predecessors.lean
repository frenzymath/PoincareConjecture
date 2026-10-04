import PoincareLib.Geometry.RicciFlow.Curvature.Theory
import PoincareLib.Geometry.RicciFlow.Harnack.Theory
import PoincareLib.Geometry.RicciFlow.Compactness.Convergence
import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.BoundsTheory

/-!
# Predecessors for controlled generalized-flow compactness

The four fields are the accepted Mapher `Statements/M30Providers.lean`
interface at `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`, with the existing
workspace name `DenseGeneralizedBoundedDistanceTheory` for the dense M29 service.
Partial compactness, carrier transport, and terminal convergence are M30 work.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

structure M30ControlledBlowupPredecessors : Prop where
  m04 : RicciFlowCurvatureTheory.{u}
  m06 : HarnackAncientTheory.{u}
  m07 : ∀ {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses 3 T' T),
    Nonempty (PointedRicciFlowCompactnessConclusion H)
  m29 : DenseGeneralizedBoundedDistanceTheory.{u}

end PoincareMT
