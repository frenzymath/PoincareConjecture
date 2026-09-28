import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Homology.IntegralCoverHomology









set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

def integralContractibleAmbientRelativeBoundaryIso
    (A : Set X) [ContractibleSpace X] (n : Nat) :
    integralRelativeHomology A (n + 2) ≅ integralHomology A (n + 1) := by
  let S := integralPairSequence_shortExact A
  exact S.δIso (n + 2) (n + 1) rfl
    (integral_contractible_homology_isZero X (n + 2) (by omega))
    (integral_contractible_homology_isZero X (n + 1) (by omega))

end Poincare.Topology
