import PoincareLib.Topology.Manifold.EmbeddedSphere.Relative.OpenEmbeddingExcision
import PoincareLib.Topology.Manifold.EmbeddedSphere.Relative.BoundaryNaturality
import PoincareLib.Topology.Manifold.EmbeddedSphere.Parity.Equiv
import Mathlib.Topology.LocalAtTarget

/-!
# Relative subspaces and triple boundaries under open embeddings

Matched subspaces inherit an open embedding. A closed support inside its
range supplies relative excision on those subspaces, which preserves and
reflects parity of the actual triple boundary. Source: Hatcher, pp. 117-119,
and M53 derivation 14, for the separation repair of Morgan--Tian,
Proposition 15.12 and Remark 15.13, p. 365.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex Topology
open Poincare.Topology

universe u

namespace PoincareMT.Topology.EmbeddedSphere

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- An open embedding between matched subspaces induces relative homology
isomorphisms when a closed support lies in its range. Neither larger
subspace must be closed. Source: Hatcher, p. 119, and M53 derivation 14. -/
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

/-- Triple-boundary parity is preserved and reflected by an open embedding
when its relative subspaces satisfy closed-support excision. The ambient
relative map need not be an isomorphism. Source: Hatcher, pp. 117-119,
and M53 derivation 14. -/
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

end PoincareMT.Topology.EmbeddedSphere
