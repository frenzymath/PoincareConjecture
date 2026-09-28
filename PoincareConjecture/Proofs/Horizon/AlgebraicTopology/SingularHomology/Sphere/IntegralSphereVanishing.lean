import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Sphere.IntegralSphereHomology
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Relative.IntegralAmbientRelative

set_option autoImplicit false

open CategoryTheory Limits Metric
open scoped ContinuousMap Topology

namespace Poincare.Topology

noncomputable section

private theorem zeroSphere_positive_homology_isZero (n : Nat) (hn : n ≠ 0) :
    IsZero (integralHomology (sphere (0 : EuclideanSpace Real (Fin 1)) 1) n) := by
  let e := (OrthonormalBasis.singleton (Fin 1) Real).repr.symm
  let eS : sphere (0 : EuclideanSpace Real (Fin 1)) 1 ≃ sphere (0 : Real) 1 :=
    e.toEquiv.subtypeEquiv (fun x => by
      simp only [mem_sphere, dist_zero_right]
      change (‖x‖ = 1) ↔ ‖e x‖ = 1
      rw [e.norm_map]
      rfl)
  have hfinite : (sphere (0 : Real) 1).Finite := by
    rw [Real.sphere_eq_pair 0 (by norm_num)]
    exact Set.toFinite _
  let : Fintype (sphere (0 : Real) 1) := hfinite.fintype
  let : Finite (sphere (0 : EuclideanSpace Real (Fin 1)) 1) :=
    Finite.of_equiv (sphere (0 : Real) 1) eS.symm
  exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat Int) n integralCoefficient
      (TopCat.of (sphere (0 : EuclideanSpace Real (Fin 1)) 1)) hn

private def sphereHomologyDegreeShiftIso (m n : Nat) :
    integralHomology (sphere (0 : EuclideanSpace Real (Fin (m + 2))) 1) (n + 2) ≅
      integralHomology (sphere (0 : EuclideanSpace Real (Fin (m + 1))) 1) (n + 1) := by
  apply Classical.choice
  obtain ⟨A, B, hA, hB, hcover, hAc, hBc, ⟨hAB⟩⟩ :=
    exists_sphere_contractible_open_cover m
  let : ContractibleSpace A := hAc
  let : ContractibleSpace B := hBc
  exact ⟨integralContractibleCoverHomologyIso A B hA hB hcover n ≪≫
    integralHomologyIsoOfHomotopyEquiv
      (((intersectionPreimageHomeomorph A B).symm.toHomotopyEquiv).trans hAB) (n + 1)⟩

theorem integralSphereS2HomologyThree_isZero :
    IsZero (integralHomology (sphere (0 : EuclideanSpace Real (Fin 3)) 1) 3) :=
  (zeroSphere_positive_homology_isZero 1 (by decide)).of_iso
    (sphereHomologyDegreeShiftIso 1 1 ≪≫ sphereHomologyDegreeShiftIso 0 0)

theorem integralPuncturedEuclideanRelativeFour_isZero :
    IsZero (integralRelativeHomology
      ({0}ᶜ : Set (EuclideanSpace Real (Fin 3))) 4) := by
  let E := EuclideanSpace Real (Fin 3)
  let e : integralRelativeHomology ({0}ᶜ : Set E) 4 ≅
      integralHomology (sphere (0 : E) 1) 3 :=
    integralContractibleAmbientRelativeBoundaryIso ({0}ᶜ : Set E) 2 ≪≫
      integralHomologyIsoOfHomotopyEquiv (puncturedSpaceSphereHomotopyEquiv E) 3
  exact integralSphereS2HomologyThree_isZero.of_iso e

theorem integralSphereS2HomologyAbove_isZero (n : Nat) :
    IsZero (integralHomology
      (sphere (0 : EuclideanSpace Real (Fin 3)) 1) (n + 3)) :=
  (zeroSphere_positive_homology_isZero (n + 1) (by omega)).of_iso
    (sphereHomologyDegreeShiftIso 1 (n + 1) ≪≫ sphereHomologyDegreeShiftIso 0 n)

theorem integralPuncturedEuclideanRelativeAbove_isZero (n : Nat) :
    IsZero (integralRelativeHomology
      ({0}ᶜ : Set (EuclideanSpace Real (Fin 3))) (n + 4)) := by
  let E := EuclideanSpace Real (Fin 3)
  let e : integralRelativeHomology ({0}ᶜ : Set E) (n + 4) ≅
      integralHomology (sphere (0 : E) 1) (n + 3) :=
    integralContractibleAmbientRelativeBoundaryIso ({0}ᶜ : Set E) (n + 2) ≪≫
      integralHomologyIsoOfHomotopyEquiv (puncturedSpaceSphereHomotopyEquiv E) (n + 3)
  exact (integralSphereS2HomologyAbove_isZero n).of_iso e

end

end Poincare.Topology
