import PoincareConjecture.Definitions.M53SphereSeparation
import PoincareConjecture.Proofs.M02.Topology.IntegralHomologyUniverse
import PoincareConjecture.Proofs.M02.Topology.IntegralSphereBase
import PoincareConjecture.Proofs.M53.Mathlib.EvenEquiv
import Mathlib.Algebra.Group.Int.Even













set_option autoImplicit false

noncomputable section

open CategoryTheory
open PoincareConjecture.Proofs.M02.Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M53

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  (S : SmoothEmbeddedNullHomotopicSphere (M := M))



def sphereRangeHomologyEquiv : integralHomology (Set.range S.sphere) 2 ≃ₗ[Int] Int :=
  (integralHomeomorphHomologyEquiv S.smooth_embedding.isEmbedding.toHomeomorph.symm 2).trans
    (integralSphereH2Iso.toLinearEquiv.trans ULift.moduleEquiv)



def sphereFundamentalClass : integralHomology (Set.range S.sphere) 2 :=
  (sphereRangeHomologyEquiv S).symm 1



theorem sphereFundamentalClass_not_even : ¬ Even (sphereFundamentalClass S) := by
  intro h
  apply Int.not_even_one
  have he : (sphereRangeHomologyEquiv S).toAddEquiv (sphereFundamentalClass S) = 1 :=
    (sphereRangeHomologyEquiv S).apply_symm_apply 1
  rw [← he]
  exact ((sphereRangeHomologyEquiv S).toAddEquiv.even_apply_iff _).mpr h




theorem sphereRange_puncture_contractible (x : Set.range S.sphere) :
    ContractibleSpace ({x}ᶜ : Set (Set.range S.sphere)) := by
  let e := S.smooth_embedding.isEmbedding.toHomeomorph.symm
  let ep : ({x}ᶜ : Set (Set.range S.sphere)) ≃ₜ ({e x}ᶜ : Set UnitTwoSphere) :=
    e.subtype (fun y => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, e.injective.eq_iff])
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  obtain ⟨p, _⟩ := exists_sphere_puncture_homeomorph 2 (e x)
  exact (ep.trans p).contractibleSpace




theorem sphereRange_toLocalHomology_isIso (x : Set.range S.sphere) :
    IsIso (integralToRelativeHomology ({x}ᶜ : Set (Set.range S.sphere)) 2) := by
  let := sphereRange_puncture_contractible S x
  exact integralToRelativeHomology_isIso_of_contractible _ 1




theorem sphereFundamentalClass_local_not_even (x : Set.range S.sphere) :
    ¬ Even (integralToRelativeHomology ({x}ᶜ : Set (Set.range S.sphere)) 2
      (sphereFundamentalClass S)) := by
  let := sphereRange_toLocalHomology_isIso S x
  let e := (asIso (integralToRelativeHomology ({x}ᶜ : Set (Set.range S.sphere)) 2)).toLinearEquiv
  intro h
  exact sphereFundamentalClass_not_even S (e.toAddEquiv.even_apply_iff _ |>.mp h)

end PoincareConjecture.Proofs.M53
