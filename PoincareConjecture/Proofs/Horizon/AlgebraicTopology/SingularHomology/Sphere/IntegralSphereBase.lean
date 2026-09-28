import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Sphere.IntegralZeroSphere
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Sphere.IntegralSphereHomology

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Metric
open scoped ContinuousMap Topology

universe u

namespace Poincare.Topology

def integralSphereH1Iso :
    integralHomology (sphere (0 : EuclideanSpace Real (Fin 2)) 1) 1 ≅
      integralCoefficient := by
  apply Classical.choice
  obtain ⟨A, B, hA, hB, hcover, hAc, hBc, ⟨hAB⟩⟩ :=
    exists_sphere_contractible_open_cover 0
  let : ContractibleSpace A := hAc
  let : ContractibleSpace B := hBc
  let AB : Set B := (Subtype.val : B → sphere (0 : EuclideanSpace Real (Fin 2)) 1) ⁻¹' A
  let eCover := integralContractibleCoverHomologyOneIso A B hA hB hcover
  let eInter : AB ≃ₕ sphere (0 : EuclideanSpace Real (Fin 1)) 1 :=
    ((intersectionPreimageHomeomorph A B).symm.toHomotopyEquiv).trans hAB
  let eH0 := integralHomologyIsoOfHomotopyEquiv eInter 0
  let iAB : C(AB, B) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let eKernelB := integralHomologyZeroMapKernelIso iAB
  let eKernelS :
      kernel (integralHomologyZeroAugmentation AB) ≅
        kernel (integralHomologyZeroAugmentation
          (sphere (0 : EuclideanSpace Real (Fin 1)) 1)) := by
    apply kernel.mapIso (integralHomologyZeroAugmentation AB)
      (integralHomologyZeroAugmentation
      (sphere (0 : EuclideanSpace Real (Fin 1)) 1)) eH0 (Iso.refl _)
    change integralHomologyZeroAugmentation AB ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact (integralHomologyZeroAugmentation_natural eInter.toFun).symm
  exact ⟨eCover ≪≫ eKernelB ≪≫ eKernelS ≪≫
    integralZeroSphereAugmentationKernelIso⟩

def integralSphereH2Iso :
    integralHomology (sphere (0 : EuclideanSpace Real (Fin 3)) 1) 2 ≅
      integralCoefficient :=
  integralSphereHomologySuccIso 0 ≪≫ integralSphereH1Iso

def integralSphereH3Iso :
    integralHomology (sphere (0 : EuclideanSpace Real (Fin 4)) 1) 3 ≅
      integralCoefficient :=
  integralSphereHomologySuccIso 1 ≪≫ integralSphereH2Iso

end Poincare.Topology
