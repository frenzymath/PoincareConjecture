import PoincareConjecture.Proofs.M53.Prop15_12_BoundaryNaturality
import PoincareConjecture.Proofs.M02.Topology.IntegralSupportLocalization











set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex
open PoincareConjecture.Proofs.M02.Topology

universe u

namespace PoincareConjecture.Proofs.M53

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]



theorem integralRelativeMap_id_eq_restriction {A B : Set X} (h : A ⊆ B) :
    integralRelativeMap (ContinuousMap.id X) h = integralRelativeRestriction h := by
  apply (cancel_epi (integralRelativeProjection A)).mp
  rw [integralRelativeMap_projection (ContinuousMap.id X) h,
    integralRelativeRestriction_projection h]
  change integralChainsFunctor.map (𝟙 (TopCat.of X)) ≫ integralRelativeProjection B = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]



theorem integralRelativeMap_restriction_naturality
    (f : C(X, Y)) {A A' : Set X} {B B' : Set Y}
    (hf : Set.MapsTo f A B) (hf' : Set.MapsTo f A' B')
    (hA : A ⊆ A') (hB : B ⊆ B') :
    integralRelativeMap f hf ≫ integralRelativeRestriction hB =
      integralRelativeRestriction hA ≫ integralRelativeMap f hf' := by
  apply (cancel_epi (integralRelativeProjection A)).mp
  rw [← Category.assoc, integralRelativeMap_projection, Category.assoc,
    integralRelativeRestriction_projection, ← Category.assoc,
    integralRelativeRestriction_projection, integralRelativeMap_projection]





theorem integralTripleBoundary_after_restriction
    {S A B : Set X} (hSA : S ⊆ A) (hBA : B ⊆ A) (n : Nat) :
    homologyMap (integralRelativeRestriction hSA) (n + 1) ≫
        integralTripleBoundary A B hBA n =
      integralRelativeBoundary S n ≫
        integralToRelativeHomology ((Subtype.val : S → X) ⁻¹' B) n ≫
          homologyMap (integralRelativeMap (ContinuousMap.inclusion hSA)
            (A := (Subtype.val : S → X) ⁻¹' B)
            (B := (Subtype.val : A → X) ⁻¹' B) (fun _ hx => hx)) n := by
  have hnat := integralRelativeBoundary_naturality (ContinuousMap.id X) hSA n
  change integralRelativeBoundary S n ≫
      homologyMap (integralChainsFunctor.map (TopCat.ofHom (ContinuousMap.inclusion hSA))) n =
    homologyMap (integralRelativeMap (ContinuousMap.id X) hSA) (n + 1) ≫
      integralRelativeBoundary A n at hnat
  rw [integralRelativeMap_id_eq_restriction] at hnat
  have hπ : integralToRelativeHomology ((Subtype.val : S → X) ⁻¹' B) n ≫
      homologyMap (integralRelativeMap (ContinuousMap.inclusion hSA)
        (A := (Subtype.val : S → X) ⁻¹' B)
        (B := (Subtype.val : A → X) ⁻¹' B) (fun _ hx => hx)) n =
      homologyMap (integralChainsFunctor.map (TopCat.ofHom (ContinuousMap.inclusion hSA))) n ≫
        integralToRelativeHomology ((Subtype.val : A → X) ⁻¹' B) n := by
    simpa only [homologyMap_comp] using congrArg (fun g => homologyMap g n)
      (integralRelativeMap_projection (ContinuousMap.inclusion hSA)
        (A := (Subtype.val : S → X) ⁻¹' B)
        (B := (Subtype.val : A → X) ⁻¹' B) (fun _ hx => hx))
  rw [integralTripleBoundary_eq_pair, ← Category.assoc, ← hnat, Category.assoc, hπ]

end PoincareConjecture.Proofs.M53
