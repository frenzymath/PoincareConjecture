import PoincareLib.Topology.Manifold.EmbeddedSphere.Relative.Triple

/-!
# Naturality of the actual pair and triple boundaries

Continuous maps of pairs give maps of the actual M02 short exact pair
sequences. Their connecting homomorphisms commute with the induced maps.
Triple boundary naturality follows by the pair-to-triple identity and
relative projection naturality. Source: Hatcher, pp. 117-118, and M53
derivation 10, for the separation repair of Morgan--Tian, Proposition
15.12 and Remark 15.13, p. 365.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex
open Poincare.Topology

universe u

namespace PoincareMT.Topology.EmbeddedSphere

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous map of pairs gives a map of the actual short exact pair
sequences. Source: Hatcher, Theorem 2.16, pp. 117-118, and M53 derivation 10. -/
def integralPairSequenceMap (f : C(X, Y)) {A : Set X} {A' : Set Y}
    (hf : Set.MapsTo f A A') : integralPairSequence A ⟶ integralPairSequence A' where
  τ₁ := integralChainsFunctor.map (TopCat.ofHom
    ((f.restrictPreimage A').comp (ContinuousMap.inclusion hf)))
  τ₂ := integralChainsFunctor.map (TopCat.ofHom f)
  τ₃ := integralRelativeMap f hf
  comm₁₂ := by
    change integralChainsFunctor.map (TopCat.ofHom
        ((f.restrictPreimage A').comp (ContinuousMap.inclusion hf))) ≫
      integralSubspaceChains A' = integralSubspaceChains A ≫
        integralChainsFunctor.map (TopCat.ofHom f)
    simp only [integralSubspaceChains, ← CategoryTheory.Functor.map_comp]
    rfl
  comm₂₃ := (integralRelativeMap_projection f hf).symm

/-- Pair boundaries commute with the actual induced maps of a continuous
map of pairs. Source: Hatcher, pp. 117-118, and M53 derivation 10. -/
theorem integralRelativeBoundary_naturality
    (f : C(X, Y)) {A : Set X} {A' : Set Y} (hf : Set.MapsTo f A A') (n : Nat) :
    integralRelativeBoundary A n ≫ homologyMap (integralChainsFunctor.map (TopCat.ofHom
        ((f.restrictPreimage A').comp (ContinuousMap.inclusion hf)))) n =
      homologyMap (integralRelativeMap f hf) (n + 1) ≫ integralRelativeBoundary A' n :=
  HomologySequence.δ_naturality (integralPairSequenceMap f hf)
    (integralPairSequence_shortExact A) (integralPairSequence_shortExact A') (n + 1) n rfl

/-- Triple boundaries commute with actual relative maps of continuous
maps of triples. Both relative subsets are pulled back to their larger
subspaces explicitly. Source: Hatcher, pp. 117-118, and M53 derivation 10. -/
theorem integralTripleBoundary_naturality
    (f : C(X, Y)) {A B : Set X} {A' B' : Set Y}
    (hBA : B ⊆ A) (hBA' : B' ⊆ A')
    (hfA : Set.MapsTo f A A') (hfB : Set.MapsTo f B B') (n : Nat) :
    integralTripleBoundary A B hBA n ≫
      homologyMap (integralRelativeMap
        ((f.restrictPreimage A').comp (ContinuousMap.inclusion hfA))
        (A := (Subtype.val : A → X) ⁻¹' B)
        (B := (Subtype.val : A' → Y) ⁻¹' B') (fun _ hx => hfB hx)) n =
      homologyMap (integralRelativeMap f hfA) (n + 1) ≫
        integralTripleBoundary A' B' hBA' n := by
  let fA := (f.restrictPreimage A').comp (ContinuousMap.inclusion hfA)
  let hAB : Set.MapsTo fA ((Subtype.val : A → X) ⁻¹' B)
      ((Subtype.val : A' → Y) ⁻¹' B') := fun _ hx => hfB hx
  have hπ : integralToRelativeHomology ((Subtype.val : A → X) ⁻¹' B) n ≫
      homologyMap (integralRelativeMap fA hAB) n =
      homologyMap (integralChainsFunctor.map (TopCat.ofHom fA)) n ≫
        integralToRelativeHomology ((Subtype.val : A' → Y) ⁻¹' B') n := by
    simpa only [homologyMap_comp] using
      congrArg (fun g => homologyMap g n) (integralRelativeMap_projection fA hAB)
  change integralTripleBoundary A B hBA n ≫ homologyMap (integralRelativeMap fA hAB) n = _
  rw [integralTripleBoundary_eq_pair, integralTripleBoundary_eq_pair,
    Category.assoc, hπ, ← Category.assoc, integralRelativeBoundary_naturality f hfA n,
    Category.assoc]

end PoincareMT.Topology.EmbeddedSphere
