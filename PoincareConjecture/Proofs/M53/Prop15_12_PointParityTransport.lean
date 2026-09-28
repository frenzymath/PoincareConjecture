import PoincareConjecture.Proofs.M53.Prop15_12_RestrictionNaturality
import PoincareConjecture.Proofs.M53.Prop15_12_OpenEmbeddingExcision
import PoincareConjecture.Proofs.M53.Mathlib.EvenEquiv

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex Topology
open PoincareConjecture.Proofs.M02.Topology

universe u

namespace PoincareConjecture.Proofs.M53

theorem even_point_restriction_openEmbedding_iff
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y]
    (f : C(X, Y)) (hf : IsOpenEmbedding f) {A : Set X} {B : Set Y}
    (hfA : Set.MapsTo f A B) (x : X)
    (hA : A ⊆ ({x}ᶜ : Set X)) (hB : B ⊆ ({f x}ᶜ : Set Y))
    (n : Nat) (a : integralRelativeHomology A n) :
    Even (homologyMap (integralRelativeRestriction hB) n
      (homologyMap (integralRelativeMap f hfA) n a)) ↔
        Even (homologyMap (integralRelativeRestriction hA) n a) := by
  have hpoint : ∀ z : X, z ∈ ({x}ᶜ : Set X) ↔ f z ∈ ({f x}ᶜ : Set Y) := by
    intro z
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hf.injective.eq_iff]
  let hp : Set.MapsTo f ({x}ᶜ : Set X) ({f x}ᶜ : Set Y) :=
    fun z hz => (hpoint z).mp hz
  let F := homologyMap (integralRelativeMap f hp) n
  let : IsIso F := integralRelativeMap_isIso_of_closed_support f hf hpoint
    isClosed_singleton (Set.singleton_subset_iff.mpr (Set.mem_range_self x))
      Set.Subset.rfl n
  have hnat : homologyMap (integralRelativeMap f hfA) n ≫
      homologyMap (integralRelativeRestriction hB) n =
      homologyMap (integralRelativeRestriction hA) n ≫ F := by
    simpa only [homologyMap_comp] using congrArg (fun g => homologyMap g n)
      (integralRelativeMap_restriction_naturality f hfA hp hA hB)
  have heq := congrArg (fun g => g a) hnat
  change Even ((homologyMap (integralRelativeMap f hfA) n ≫
    homologyMap (integralRelativeRestriction hB) n) a) ↔ _
  rw [heq]
  exact (asIso F).toLinearEquiv.toAddEquiv.even_apply_iff _

end PoincareConjecture.Proofs.M53
