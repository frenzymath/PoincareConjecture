import PoincareConjecture.Statements.M64Comparison
import PoincareConjecture.Proofs.M64.CompleteComparison
import PoincareConjecture.Proofs.M64.DiskAdapters
import PoincareConjecture.Proofs.M64.FamilyAdapters
import PoincareConjecture.Proofs.M63












set_option autoImplicit false

universe u

namespace PoincareConjecture
































































theorem m64AnnulusComparison (hM63 : M63RampEstimatesTheory.{u}) :
    M64ComparisonTheory.{u} := by
  exact m64ComparisonTheory_from_M63 hM63




theorem m64AnnulusComparison_from_predecessors : M64ComparisonTheory.{u} :=
  m64AnnulusComparison m63RampEstimates_from_predecessors

end PoincareConjecture
