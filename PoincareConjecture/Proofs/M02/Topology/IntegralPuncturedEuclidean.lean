import PoincareConjecture.Proofs.M02.Topology.IntegralAmbientRelative
import PoincareConjecture.Proofs.M02.Topology.IntegralHomologyEquiv
import PoincareConjecture.Proofs.M02.Topology.SphereOpenCover

set_option autoImplicit false

noncomputable section

open CategoryTheory Metric

universe u

namespace PoincareConjecture.Proofs.M02.Topology

def integralPuncturedEuclideanRelativeIso
    (hS : integralHomology
      (sphere (0 : EuclideanSpace Real (Fin 3)) 1) 2 ≅ integralCoefficient) :
    integralRelativeHomology
      ({0}ᶜ : Set (EuclideanSpace Real (Fin 3))) 3 ≅ integralCoefficient := by
  let E := EuclideanSpace Real (Fin 3)
  let A : Set E := ({0}ᶜ : Set E)
  exact integralContractibleAmbientRelativeBoundaryIso A 1 ≪≫
    integralHomologyIsoOfHomotopyEquiv
      (puncturedSpaceSphereHomotopyEquiv E) 2 ≪≫ hS

end PoincareConjecture.Proofs.M02.Topology
