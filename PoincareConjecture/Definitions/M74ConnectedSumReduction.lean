import PoincareConjecture.Definitions.Ch15.SurgeryTopology
import PoincareConjecture.Statement

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

structure M74ReductionInput {n : ℕ}
    (pieces : Fin n → GeneralizedSliceCarrier.{u})
    (C : GeneralizedSliceCarrier.{u}) where
  assembly : SmoothFiniteConnectedSumAssembly pieces C
  target_nonempty : Nonempty C.carrier
  target_connected : IsConnected (Set.univ : Set C.carrier)
  factor_sphere : ∀ i, Nonempty
    (Diffeomorph (𝓡 3) (𝓡 3) (pieces i).carrier ThreeSphere ∞)

structure M74ReductionConclusion (C : GeneralizedSliceCarrier.{u}) where
  reduction : Nonempty
    (Diffeomorph (𝓡 3) (𝓡 3) C.carrier ThreeSphere ∞)

end PoincareConjecture
