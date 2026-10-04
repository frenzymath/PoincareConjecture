import PoincareLib.Geometry.RicciFlow.Generalized.DenseTime
import PoincareLib.Topology.Manifold.NeckCap.Theory
import PoincareLib.Geometry.RicciFlow.Curvature.Theory

/-!
# M28 applied proof services

Theorem 10.2 is stated as an implication whose canonical-neighborhood input is
primitive. This interface records the earlier curvature and Appendix-A
services used to prove that implication. The source's partial-limit Theorem
5.6 and Proposition 5.14 are not misrepresented by the stronger M07 complete
interior compactness output.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

structure M28BoundedDistancePredecessors : Prop where
  m04 : RicciFlowCurvatureTheory.{u}
  m25 : Nonempty (RepairedNeckCapTopologyTheory.{u})

end PoincareMT
