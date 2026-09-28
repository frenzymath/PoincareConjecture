import PoincareConjecture.Statements.M72FiniteReconstruction
import PoincareConjecture.Proofs.M72.Transport
import PoincareConjecture.Proofs.M72.Cor15_4_Assembly.Assembly

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

theorem m72FiniteReconstruction :
    M72FiniteReconstructionStatement.{u} := by
  intro M _ _ _ _ _ _ _ _ N I
  exact ⟨m72ReconstructionConclusion I⟩

end PoincareConjecture
