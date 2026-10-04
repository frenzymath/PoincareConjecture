import PoincareLib.AlgebraicTopology.SingularHomology.Relative.IntegralAmbientRelative
import PoincareLib.AlgebraicTopology.SingularHomology.Homology.IntegralHomologyEquiv
import PoincareLib.Topology.Homotopy.Sphere.SphereOpenCover

/-!
# The punctured Euclidean local generator

For a chosen top-degree sphere class, the connecting morphism for the
contractible Euclidean ambient space produces the corresponding relative
class at the origin.
-/

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
