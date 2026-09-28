import PoincareConjecture.Proofs.M02.Topology.IntegralChainUniverse
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.LinearAlgebra.FreeModule.Basic









set_option autoImplicit false

noncomputable section

open CategoryTheory Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

attribute [local instance 2000] Submodule.Quotient.module

variable {X : Type u} [TopologicalSpace X]

theorem integralChains_projective (X : Type u) [TopologicalSpace X] (n : Nat) :
    CategoryTheory.Projective ((integralChains X).X n) := by
  let : Module.Free Int ((integralChains X).X n) :=
    Module.Free.of_equiv (integralChainCoordinates X n).symm
  infer_instance

def integralRelativeChainCoordinates (A : Set X) (n : Nat) :
    (integralRelativeChains A).X n ≃ₗ[Int]
      ({s : C(integralSimplex n, X) // ¬range s ⊆ A} →₀ ULift.{u} Int) := by
  classical
  let S : Set C(integralSimplex n, X) := {s | ¬range s ⊆ A}
  let F : (integralChains X).X n →ₗ[Int] (S →₀ ULift.{u} Int) :=
    (Finsupp.lsubtypeDomain S).comp (integralChainCoordinates X n).toLinearMap
  have hF (c : (integralChains X).X n) (s : S) :
      F c s = integralChainCoordinates X n c s.val := rfl
  have hsurj : Function.Surjective F := by
    intro c
    refine ⟨(integralChainCoordinates X n).symm
      ((Finsupp.supportedEquivFinsupp (R := Int) S).symm c).val, ?_⟩
    apply Finsupp.ext
    intro s
    rw [hF, LinearEquiv.apply_symm_apply]
    exact congrArg (fun f => f s)
      ((Finsupp.supportedEquivFinsupp (R := Int) S).apply_symm_apply c)
  have hker : LinearMap.ker F =
      LinearMap.range ((integralSubspaceChains A).f n).hom := by
    ext c
    rw [LinearMap.mem_ker, integral_subspace_range_iff]
    constructor
    · intro hc s hs
      by_contra h
      have he := congrArg (fun f => f ⟨s, h⟩) hc
      exact (Finsupp.mem_support_iff.mp hs) he
    · intro hc
      apply Finsupp.ext
      intro s
      rw [hF]
      by_contra h
      exact s.property (hc s.val (Finsupp.mem_support_iff.mpr h))
  exact (integralRelativeQuotientEquiv A n).trans
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans (F.quotKerEquivOfSurjective hsurj))

theorem integralRelativeChains_projective (A : Set X) (n : Nat) :
    CategoryTheory.Projective ((integralRelativeChains A).X n) := by
  let : Module.Free Int ((integralRelativeChains A).X n) :=
    Module.Free.of_equiv (integralRelativeChainCoordinates A n).symm
  infer_instance

end PoincareConjecture.Proofs.M02.Topology
