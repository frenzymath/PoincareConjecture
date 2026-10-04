import PoincareLib.Geometry.RicciFlow.Surgery.Induction.NoncollapseTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.NoncollapseData
import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Theory
import PoincareLib.Geometry.RicciFlow.Curvature.Theory
import PoincareLib.Geometry.Spacetime.GeometryTheory
import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.Geometry
import PoincareLib.Geometry.RicciFlow.Rescaling.Theory
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Theory
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.RegularHistory

/-!
# M46 repaired noncollapsing induction statement

The selected calibrated setup admits the noncollapsing extension at every
finite parameter prefix with the same initial seeds.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure M46Predecessors : Prop where
  m04 : RicciFlowCurvatureTheory.{u}
  m11 : GeneralizedSpacetimeGeometryTheory.{u} 3
  m12 : GeneralizedRicciGaugeTheory.{u} 3
  m13 : GeneralizedParabolicRescalingTheory.{u} 3
  m14 : GeneralizedLGeometryTheory.{u} 3
  m15 : GeneralizedNoncollapsingConclusion.{u} 3
  regular_history : ∀ (F : SurgeryFlowData.{u}) (W : M33RegularHistoryWindow F),
    Nonempty (M33RegularHistoryData W)

end PoincareMT
