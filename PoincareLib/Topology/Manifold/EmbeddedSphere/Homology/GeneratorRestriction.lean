import PoincareLib.Topology.Manifold.EmbeddedSphere.Homology.SphereGenerator
import PoincareLib.Topology.Manifold.EmbeddedSphere.Relative.RestrictionNaturality

/-!
# The sphere generator in the actual exterior-relative surface pair

A chosen surface point outside the exterior detects non-Evenness of the
restricted sphere generator. An actual surface inclusion isomorphism then
detects non-Evenness of the corresponding triple boundary. Source: Hatcher,
pp. 117-119 and 233-235, and M53 derivation 15, for the separation repair of
Morgan--Tian, Proposition 15.12 and Remark 15.13, p. 365.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex
open Poincare.Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.Topology.EmbeddedSphere

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  (S : SmoothEmbeddedNullHomotopicSphere (M := M))

/-- A specified surface point outside the exterior detects non-Evenness
of the actual relative image of the sphere generator. Source: Hatcher,
pp. 233-235, and M53 derivation 15. -/
theorem sphereFundamentalClass_relative_not_even
    (L : Set M) (x : Set.range S.sphere) (hx : x.val ∉ L) :
    ¬ Even (integralToRelativeHomology ((Subtype.val : Set.range S.sphere → M) ⁻¹' L) 2
      (sphereFundamentalClass S)) := by
  let B := (Subtype.val : Set.range S.sphere → M) ⁻¹' L
  have hB : B ⊆ ({x}ᶜ : Set (Set.range S.sphere)) := by
    intro y hy hxy
    have heq : y = x := hxy
    subst y
    exact hx hy
  have hπ : integralToRelativeHomology B 2 ≫
      homologyMap (integralRelativeRestriction hB) 2 =
        integralToRelativeHomology ({x}ᶜ : Set (Set.range S.sphere)) 2 := by
    simpa only [homologyMap_comp] using congrArg (fun q => homologyMap q 2)
      (integralRelativeRestriction_projection hB)
  intro h
  have he := Even.map (homologyMap (integralRelativeRestriction hB) 2).hom.toAddMonoidHom h
  change Even ((integralToRelativeHomology B 2 ≫
    homologyMap (integralRelativeRestriction hB) 2) (sphereFundamentalClass S)) at he
  rw [hπ] at he
  exact sphereFundamentalClass_local_not_even S x he

/-- A relative class bounding the sphere generator has non-Even triple
boundary whenever the actual surface inclusion is an isomorphism and a
surface point remains outside the exterior. Source: Hatcher, pp. 117-119
and 233-235, and M53 derivation 15. -/
theorem sphere_tripleBoundary_restriction_not_even
    {A L : Set M} (hSA : Set.range S.sphere ⊆ A) (hLA : L ⊆ A)
    (x : Set.range S.sphere) (hx : x.val ∉ L)
    (a : integralRelativeHomology (Set.range S.sphere) 3)
    (ha : integralRelativeBoundary (Set.range S.sphere) 2 a = sphereFundamentalClass S)
    (hj : IsIso (homologyMap (integralRelativeMap (ContinuousMap.inclusion hSA)
      (A := (Subtype.val : Set.range S.sphere → M) ⁻¹' L)
      (B := (Subtype.val : A → M) ⁻¹' L) (fun _ hz => hz)) 2)) :
    ¬ Even (integralTripleBoundary A L hLA 2
      (homologyMap (integralRelativeRestriction hSA) 3 a)) := by
  let J := homologyMap (integralRelativeMap (ContinuousMap.inclusion hSA)
    (A := (Subtype.val : Set.range S.sphere → M) ⁻¹' L)
    (B := (Subtype.val : A → M) ⁻¹' L) (fun _ hz => hz)) 2
  let : IsIso J := hj
  have heq := congrArg (fun q => q a) (integralTripleBoundary_after_restriction hSA hLA 2)
  change integralTripleBoundary A L hLA 2
      (homologyMap (integralRelativeRestriction hSA) 3 a) =
    J (integralToRelativeHomology ((Subtype.val : Set.range S.sphere → M) ⁻¹' L) 2
      (integralRelativeBoundary (Set.range S.sphere) 2 a)) at heq
  rw [ha] at heq
  rw [heq]
  intro h
  exact sphereFundamentalClass_relative_not_even S L x hx
    ((asIso J).toLinearEquiv.toAddEquiv.even_apply_iff _ |>.mp h)

end PoincareMT.Topology.EmbeddedSphere
