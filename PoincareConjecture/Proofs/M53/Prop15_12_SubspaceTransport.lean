import PoincareConjecture.Proofs.M53.Prop15_12_OpenEmbeddingExcision
import PoincareConjecture.Proofs.M53.Prop15_12_BoundaryNaturality
import PoincareConjecture.Proofs.M53.Mathlib.EvenEquiv
import Mathlib.Topology.LocalAtTarget











set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex Topology
open PoincareConjecture.Proofs.M02.Topology

universe u

namespace PoincareConjecture.Proofs.M53

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]




theorem integralRelativeMap_subspace_isIso_of_closed_support
    (f : C(X, Y)) (hf : IsOpenEmbedding f) {A B : Set X} {A' B' K : Set Y}
    (hA : ∀ x, x ∈ A ↔ f x ∈ A') (hB : ∀ x, x ∈ B ↔ f x ∈ B')
    (hK : IsClosed K) (hKr : K ⊆ Set.range f) (hKB : Kᶜ ⊆ B') (n : Nat) :
    IsIso (homologyMap (integralRelativeMap
      ((f.restrictPreimage A').comp (ContinuousMap.inclusion (fun x hx => (hA x).mp hx)))
      (A := (Subtype.val : A → X) ⁻¹' B)
      (B := (Subtype.val : A' → Y) ⁻¹' B') (fun x hx => (hB x.val).mp hx)) n) := by
  let fA := (f.restrictPreimage A').comp
    (ContinuousMap.inclusion (fun x hx => (hA x).mp hx))
  have hfA : IsOpenEmbedding fA := by
    have heq : A = f ⁻¹' A' := Set.ext hA
    subst A
    exact hf.restrictPreimage A'
  have hrel : ∀ x : A, x ∈ (Subtype.val : A → X) ⁻¹' B ↔
      fA x ∈ (Subtype.val : A' → Y) ⁻¹' B' := fun x => hB x.val
  have hrange : (Subtype.val : A' → Y) ⁻¹' K ⊆ Set.range fA := by
    intro y hy
    obtain ⟨x, hx⟩ := hKr hy
    have hxA : x ∈ A := (hA x).mpr (hx ▸ y.property)
    exact ⟨⟨x, hxA⟩, Subtype.ext hx⟩
  exact integralRelativeMap_isIso_of_closed_support fA hfA hrel
    (hK.preimage continuous_subtype_val) hrange (fun _ hx => hKB hx) n





theorem even_tripleBoundary_openEmbedding_iff
    (f : C(X, Y)) (hf : IsOpenEmbedding f) {A B : Set X} {A' B' K : Set Y}
    (hBA : B ⊆ A) (hBA' : B' ⊆ A')
    (hA : ∀ x, x ∈ A ↔ f x ∈ A') (hB : ∀ x, x ∈ B ↔ f x ∈ B')
    (hK : IsClosed K) (hKr : K ⊆ Set.range f) (hKB : Kᶜ ⊆ B')
    (n : Nat) (a : integralRelativeHomology A (n + 1)) :
    Even (integralTripleBoundary A' B' hBA' n
      (homologyMap (integralRelativeMap f (fun x hx => (hA x).mp hx)) (n + 1) a)) ↔
        Even (integralTripleBoundary A B hBA n a) := by
  let F := homologyMap (integralRelativeMap
    ((f.restrictPreimage A').comp (ContinuousMap.inclusion (fun x hx => (hA x).mp hx)))
    (A := (Subtype.val : A → X) ⁻¹' B)
    (B := (Subtype.val : A' → Y) ⁻¹' B') (fun x hx => (hB x.val).mp hx)) n
  let : IsIso F := integralRelativeMap_subspace_isIso_of_closed_support
    f hf hA hB hK hKr hKB n
  have hnat : integralTripleBoundary A B hBA n ≫ F =
      homologyMap (integralRelativeMap f (fun x hx => (hA x).mp hx)) (n + 1) ≫
        integralTripleBoundary A' B' hBA' n :=
    integralTripleBoundary_naturality f hBA hBA'
      (fun x hx => (hA x).mp hx) (fun x hx => (hB x).mp hx) n
  have heq := congrArg (fun g => g a) hnat
  change Even ((homologyMap (integralRelativeMap f (fun x hx => (hA x).mp hx)) (n + 1) ≫
    integralTripleBoundary A' B' hBA' n) a) ↔ _
  rw [← heq]
  exact (asIso F).toLinearEquiv.toAddEquiv.even_apply_iff _

end PoincareConjecture.Proofs.M53
