import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.AnalyticSuppliers
import PoincareConjecture.Proofs.M30.Thm11_8.GeometricLongConvergence









set_option autoImplicit false

open scoped ENNReal

universe u

namespace PoincareConjecture.M30




theorem exists_geometric_long_convergence
    (P : M30ControlledBlowupPredecessors.{u})
    (S : GeneralizedBlowupSequence.{u}) {T₀ : ℝ≥0∞}
    (H : M30GeometricLongControls S T₀) :
    Nonempty (GeneralizedBlowupConvergence S (blowupBackwardInterval T₀)) := by
  exact exists_geometric_long_generalizedBlowupConvergence P
    withinFlowJetBoundsService withinBilinearFlowService
    spatialSliceJetConvergenceService S H

end PoincareConjecture.M30
