import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Relative.IntegralAmbientRelative
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Homology.IntegralHomologyEquiv
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Sphere.SphereOpenCover








set_option autoImplicit false

noncomputable section

open CategoryTheory Metric

universe u

namespace Poincare.Topology

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

end Poincare.Topology
