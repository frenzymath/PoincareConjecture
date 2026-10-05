import PoincareLib.AlgebraicTopology.SingularHomology.Orientation.IntegralOpenOrientation
import PoincareLib.AlgebraicTopology.SingularHomology.Orientation.IntegralOrientationCover

/-!
# Local integral homology maps

These are point-supported versions of M02's actual relative singular chain
maps. Specifying the target point directly removes image-singleton casts
from the orientation arguments. The construction follows Hatcher,
Section 3.3, pp. 233-235.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory HomologicalComplex Set
open scoped Topology

universe u

namespace Poincare.Topology.Orientation.ProjectivePlane

open Poincare.Topology

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

/-- Integral homology supported at a point, as in Hatcher, p. 234. -/
abbrev LocalHomology (X : Type u) [TopologicalSpace X] (x : X) (d : Nat) :=
  integralSupportHomology ({x} : Set X) d

/-- An injective continuous map sends the punctured pair at `x` to the
punctured pair at its image. Source: Hatcher, Section 3.3, p. 234. -/
def localChainsMap (f : C(X, Y)) (hf : Function.Injective f) (x : X) :
    integralSupportChains ({x} : Set X) ⟶
      integralSupportChains ({f x} : Set Y) :=
  integralRelativeMap f (by
    intro z hz h
    exact hz (hf h))

/-- Functoriality on local integral homology. Source: Hatcher, p. 234. -/
def localHomologyMap (f : C(X, Y)) (hf : Function.Injective f) (x : X) (d : Nat) :
    LocalHomology X x d ⟶ LocalHomology Y (f x) d :=
  homologyMap (localChainsMap f hf x) d

/-- The point map is induced by the ordinary singular-chain map.
Source: Hatcher, Section 2.1, relative homology. -/
@[reassoc]
theorem localChainsMap_projection (f : C(X, Y)) (hf : Function.Injective f) (x : X) :
    integralRelativeProjection ({x}ᶜ : Set X) ≫ localChainsMap f hf x =
      integralChainsFunctor.map (TopCat.ofHom f) ≫
        integralRelativeProjection ({f x}ᶜ : Set Y) :=
  integralRelativeMap_projection _ _

/-- The point-supported chain map of the identity is the identity.
Source: functoriality of relative homology, Hatcher, Section 2.1. -/
@[simp]
theorem localChainsMap_id (x : X) :
    localChainsMap (ContinuousMap.id X) Function.injective_id x =
      𝟙 (integralSupportChains ({x} : Set X)) := by
  apply (cancel_epi (integralRelativeProjection ({x}ᶜ : Set X))).mp
  rw [localChainsMap_projection, Category.comp_id]
  change integralChainsFunctor.map (𝟙 (TopCat.of X)) ≫ _ = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- Composition of maps on punctured pairs.
Source: functoriality of relative homology, Hatcher, Section 2.1. -/
@[reassoc]
theorem localChainsMap_comp (f : C(X, Y)) (g : C(Y, Z))
    (hf : Function.Injective f) (hg : Function.Injective g) (x : X) :
    localChainsMap f hf x ≫ localChainsMap g hg (f x) =
      localChainsMap (g.comp f) (hg.comp hf) x :=
  integralRelativeMap_comp _ _ _ _

/-- The identity acts identically on local homology.
Source: Hatcher, Section 2.1, functoriality. -/
@[simp]
theorem localHomologyMap_id (x : X) (d : Nat) :
    localHomologyMap (ContinuousMap.id X) Function.injective_id x d =
      𝟙 (LocalHomology X x d) := by
  rw [localHomologyMap, localChainsMap_id, homologyMap_id]

/-- Composition acts by composition on local homology.
Source: Hatcher, Section 2.1, functoriality. -/
@[reassoc]
theorem localHomologyMap_comp (f : C(X, Y)) (g : C(Y, Z))
    (hf : Function.Injective f) (hg : Function.Injective g) (x : X) (d : Nat) :
    localHomologyMap f hf x d ≫ localHomologyMap g hg (f x) d =
      localHomologyMap (g.comp f) (hg.comp hf) x d := by
  rw [localHomologyMap, localHomologyMap, ← homologyMap_comp, localChainsMap_comp]
  rfl

/-- The point map agrees with M02's support embedding map followed by the
canonical identification of the image singleton. Source: Hatcher, p. 234. -/
theorem localChainsMap_eq_embedding (f : C(X, Y)) (hf : Function.Injective f) (x : X) :
    localChainsMap f hf x = integralSupportEmbeddingChains f hf ({x} : Set X) ≫
      (integralRelativeSetIso
        (congrArg (fun K : Set Y => Kᶜ) (image_singleton (f := f) (a := x)))).hom := by
  apply (cancel_epi (integralRelativeProjection ({x}ᶜ : Set X))).mp
  rw [localChainsMap_projection, ← Category.assoc,
    integralSupportEmbeddingChains_projection, Category.assoc,
    integralRelativeSetIso_projection]

/-- Open excision makes an open embedding an isomorphism on local homology.
Source: Hatcher, Section 3.3, p. 234. -/
theorem localHomologyMap_isIso [T2Space Y]
    (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f) (x : X) (d : Nat) :
    IsIso (localHomologyMap f hf.injective x d) := by
  let : IsIso (homologyMap
      (integralSupportEmbeddingChains f hf.injective ({x} : Set X)) d) :=
    integralSupportEmbeddingChains_homology_isIso f hf ⟨{x}, isCompact_singleton⟩ d
  rw [localHomologyMap, localChainsMap_eq_embedding, homologyMap_comp]
  have : IsIso (homologyMap (integralRelativeSetIso
      (congrArg (fun K : Set Y => Kᶜ) (image_singleton (f := f) (a := x)))).hom d) := by
    change IsIso ((homologyFunctor (ModuleCat.{u} Int) (ComplexShape.down Nat) d).map _)
    infer_instance
  infer_instance

/-- The excision equivalence at a point for an open embedding.
Source: Hatcher, Section 3.3, p. 234. -/
def localHomologyEquiv [T2Space Y]
    (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f) (x : X) (d : Nat) :
    LocalHomology X x d ≃ₗ[Int] LocalHomology Y (f x) d := by
  let := localHomologyMap_isIso f hf x d
  exact (asIso (localHomologyMap f hf.injective x d)).toLinearEquiv

/-- The existing M02 orientation pullback is inverse to the point map.
Source: Hatcher, Section 3.3, p. 234, local excision. -/
theorem localHomologyMap_openOrientation [T2Space X] [T2Space Y]
    [LocallyCompactSpace X] (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f)
    (omega : ∀ y : Y, LocalHomology Y y 3) (x : X) :
    localHomologyMap f hf.injective x 3 (integralOpenOrientation f hf omega x) =
      omega (f x) := by
  let hK : f '' ({x} : Set X) ⊆ ({f x} : Set Y) := by
    rintro _ ⟨z, rfl, rfl⟩
    rfl
  let e := integralRelativeSetIso
    (congrArg (fun K : Set Y => Kᶜ) (image_singleton (f := f) (a := x)))
  have hid : integralSupportRestriction hK ≫ e.hom =
      𝟙 (integralSupportChains ({f x} : Set Y)) := by
    apply (cancel_epi (integralRelativeProjection ({f x}ᶜ : Set Y))).mp
    rw [← Category.assoc, integralSupportRestriction_projection,
      integralRelativeSetIso_projection, Category.comp_id]
  have hH : integralSupportHomologyRestriction hK 3 ≫ homologyMap e.hom 3 = 𝟙 _ := by
    rw [integralSupportHomologyRestriction, ← homologyMap_comp, hid, homologyMap_id]
  rw [localHomologyMap, localChainsMap_eq_embedding, homologyMap_comp,
    ModuleCat.comp_apply, integralOpenOrientation_point]
  exact congrArg (fun k => k (omega (f x))) hH

/-- Support restrictions commute with an injective map at a point.
Source: naturality of relative homology, Hatcher, Sections 2.1 and 3.3. -/
theorem localHomologyMap_restriction
    (f : C(X, Y)) (hf : Function.Injective f) {K : Set X} (x : X)
    (hx : x ∈ K) (d : Nat) :
    integralSupportHomologyRestriction (singleton_subset_iff.mpr hx) d ≫
        localHomologyMap f hf x d =
      homologyMap (integralSupportEmbeddingChains f hf K) d ≫
        integralSupportHomologyRestriction
          (singleton_subset_iff.mpr (mem_image_of_mem f hx)) d := by
  rw [localHomologyMap, integralSupportHomologyRestriction,
    integralSupportHomologyRestriction, ← homologyMap_comp, ← homologyMap_comp]
  congr 1
  apply (cancel_epi (integralRelativeProjection Kᶜ)).mp
  rw [← Category.assoc, integralSupportRestriction_projection,
    localChainsMap, integralRelativeMap_projection,
    ← Category.assoc, integralSupportEmbeddingChains_projection,
    Category.assoc, integralSupportRestriction_projection]

/-- A homotopy of punctured pairs induces equal maps on local homology.
Source: Hatcher, Section 2.1, homotopy invariance for pairs. -/
theorem relativeHomologyMap_eq_of_homotopy
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)
    {A : Set X} {B : Set Y} (hf : MapsTo f A B) (hg : MapsTo g A B)
    (hH : ∀ t : unitInterval, MapsTo (fun x => H (t, x)) A B) (d : Nat) :
    homologyMap (integralRelativeMap f hf) d =
      homologyMap (integralRelativeMap g hg) d := by
  obtain ⟨h⟩ := integral_relative_homotopy H hf hg hH
  exact h.homologyMap_eq d

end Poincare.Topology.Orientation.ProjectivePlane
