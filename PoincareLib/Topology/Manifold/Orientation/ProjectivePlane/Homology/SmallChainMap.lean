import PoincareLib.AlgebraicTopology.SingularHomology.Chains.IntegralSmallChains

/-!
# Maps of small integral singular chains

A map carrying each cover member into a specified target member preserves
the small-chain subcomplex. This supplies the chain map used in the
reflection/Mayer--Vietoris degree calculation. Source: Hatcher, Section 2.1
(small chains and excision) and Section 2.2, p. 134 (reflection degree).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

universe u v w

namespace Poincare.Topology.Orientation.ProjectivePlane

open Poincare.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {I : Type v} {J : Type w}

/-- A map subordinate to covers preserves the small-chain submodules.
Source: Hatcher, Section 2.1, the small-chain proof of excision. -/
theorem integralSmallChains_map_le (U : I → Set X) (V : J → Set Y)
    (r : I → J) (f : C(X, Y)) (hf : ∀ i, Set.MapsTo f (U i) (V (r i))) (n : Nat) :
    integralSmallChains U n ≤ (integralSmallChains V n).comap
      ((integralChainsFunctor.map (TopCat.ofHom f)).f n).hom := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, rfl⟩
  change (integralChainsFunctor.map (TopCat.ofHom f)).f n
    (integralSingularGenerator s.val (ULift.up 1)) ∈ integralSmallChains V n
  have he := congrArg (fun g => g (ULift.up 1)) (integralSingularGenerator_map s.val f)
  rw [ModuleCat.comp_apply] at he
  rw [he]
  apply Submodule.subset_span
  refine ⟨⟨f.comp s.val, ?_⟩, rfl⟩
  obtain ⟨i, hi⟩ := s.property
  refine ⟨r i, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact hf i (hi ⟨z, rfl⟩)

/-- Restriction of the singular-chain map to the small-chain subcomplex.
Source: Hatcher, Section 2.1, excision. -/
def integralSmallChainsMap (U : I → Set X) (V : J → Set Y)
    (r : I → J) (f : C(X, Y)) (hf : ∀ i, Set.MapsTo f (U i) (V (r i))) :
    integralSmallChainComplex U ⟶ integralSmallChainComplex V where
  f n := by
    letI : Module Int (integralSmallChains U n) := (integralSmallChains U n).module
    letI : Module Int (integralSmallChains V n) := (integralSmallChains V n).module
    exact ModuleCat.ofHom (LinearMap.codRestrict (integralSmallChains V n)
      (((integralChainsFunctor.map (TopCat.ofHom f)).f n).hom.domRestrict
        (integralSmallChains U n))
      (fun c => integralSmallChains_map_le U V r f hf n c.property))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg (fun g => g c.val)
      ((integralChainsFunctor.map (TopCat.ofHom f)).comm i j)

/-- Inclusion of small chains commutes with the induced map.
Source: Hatcher, Section 2.1, excision. -/
@[reassoc]
theorem integralSmallChainsMap_inclusion (U : I → Set X) (V : J → Set Y)
    (r : I → J) (f : C(X, Y)) (hf : ∀ i, Set.MapsTo f (U i) (V (r i))) :
    integralSmallChainsMap U V r f hf ≫ integralSmallChainInclusion V =
      integralSmallChainInclusion U ≫ integralChainsFunctor.map (TopCat.ofHom f) := by
  ext n c
  rfl

end Poincare.Topology.Orientation.ProjectivePlane
