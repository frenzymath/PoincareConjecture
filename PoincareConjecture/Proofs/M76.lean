import PoincareConjecture.Proofs.M76.Horizon.Compatible
import PoincareConjecture.Statements.M76SmoothingBridge










set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture


theorem m76CompatibleSmoothing : M76SmoothingStatement.{u} := by
  exact horizon_m76CompatibleSmoothing

end PoincareConjecture
