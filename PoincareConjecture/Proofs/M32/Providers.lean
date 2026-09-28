import PoincareConjecture.Proofs.M19
import PoincareConjecture.Proofs.M20.Providers
import PoincareConjecture.Proofs.M25
import PoincareConjecture.Proofs.M28
import PoincareConjecture.Proofs.M29
import PoincareConjecture.Proofs.M30.Providers
import PoincareConjecture.Proofs.M32









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture





theorem m32HornSelectionPredecessors : RepairedHornSelectionPredecessors.{u} := by
  refine {
    m04 := ricciFlowCurvatureTheory
    m19_round := ?_
    m29 := m29GeneralizedBoundedDistance
      (m28BoundedDistance ⟨ricciFlowCurvatureTheory, m25NeckCapTopology⟩)
    m30 := m30ControlledGeneralizedBlowupLimitsFromMilestones
  }
  intro N _ _ _ _ _ _ _ _ _ K
  exact (twoDimensionalClassificationTheory
    (m20TwoDimensionalPredecessors (N := N))).ancient_classification K




theorem m32HornSelectionFromMilestones : RepairedHornSelectionTheory.{u} :=
  m32HornSelection m32HornSelectionPredecessors

end PoincareConjecture
