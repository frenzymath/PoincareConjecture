import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Homology.IntegralCoverHomology
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Homology.IntegralHomologyEquiv
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Sphere.SphereOpenCover

set_option autoImplicit false

noncomputable section

open CategoryTheory Metric
open scoped ContinuousMap Topology

universe u

namespace Poincare.Topology

def intersectionPreimageHomeomorph
    {X : Type u} [TopologicalSpace X] (A B : Set X) :
    ↥(A ∩ B) ≃ₜ ((Subtype.val : B → X) ⁻¹' A) where
  toFun x := ⟨⟨x.val, x.property.2⟩, x.property.1⟩
  invFun x := ⟨x.val.val, x.property, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def integralSphereHomologySuccIso (n : Nat) :
    integralHomology (sphere (0 : EuclideanSpace Real (Fin (n + 3))) 1) (n + 2) ≅
      integralHomology (sphere (0 : EuclideanSpace Real (Fin (n + 2))) 1) (n + 1) := by
  apply Classical.choice
  obtain ⟨A, B, hA, hB, hcover, hAc, hBc, ⟨hAB⟩⟩ :=
    exists_sphere_contractible_open_cover (n + 1)
  let : ContractibleSpace A := hAc
  let : ContractibleSpace B := hBc
  exact ⟨integralContractibleCoverHomologyIso A B hA hB hcover n ≪≫
    integralHomologyIsoOfHomotopyEquiv
      (((intersectionPreimageHomeomorph A B).symm.toHomotopyEquiv).trans hAB) (n + 1)⟩

end Poincare.Topology
