import PoincareLib.Topology.Manifold.EmbeddedSphere.Relative.Excision

/-!
# Excision for actual open embeddings

Factor an open embedding through its range. The relative homeomorphism
and interior-cover excision show that its actual relative map induces
homology isomorphisms. Source: Hatcher, Theorem 2.20, p. 119, and M53
derivation 11, for the separation repair of Morgan--Tian, Proposition
15.12 and Remark 15.13, p. 365.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex Topology
open Poincare.Topology

universe u

namespace PoincareMT.Topology.EmbeddedSphere

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- An actual open embedding is an excision equivalence when its range
and the interior of the target relative subset cover the target.
Source: Hatcher, Theorem 2.20, p. 119, and M53 derivation 11. -/
theorem integralRelativeMap_isIso_of_isOpenEmbedding
    (f : C(X, Y)) (hf : IsOpenEmbedding f) {A : Set X} {B : Set Y}
    (hAB : ∀ x, x ∈ A ↔ f x ∈ B)
    (hcover : interior B ∪ Set.range f = Set.univ) (n : Nat) :
    IsIso (homologyMap (integralRelativeMap f (fun x hx => (hAB x).mp hx)) n) := by
  let e := hf.isEmbedding.toHomeomorph
  let B' : Set (Set.range f) := (Subtype.val : Set.range f → Y) ⁻¹' B
  let E := integralRelativeHomeomorphIso e A B' hAB
  have hE : integralRelativeProjection A ≫ E.hom =
      integralChainsFunctor.map (TopCat.ofHom (e : C(X, Set.range f))) ≫
        integralRelativeProjection B' := integralRelativeHomeomorphIso_projection e A B' hAB
  have hfπ : integralRelativeProjection A ≫
      integralRelativeMap f (fun x hx => (hAB x).mp hx) =
        integralChainsFunctor.map (TopCat.ofHom f) ≫ integralRelativeProjection B :=
    integralRelativeMap_projection f (fun x hx => (hAB x).mp hx)
  have hfactor : E.hom ≫ integralPairInclusion B (Set.range f) =
      integralRelativeMap f (fun x hx => (hAB x).mp hx) := by
    apply (cancel_epi (integralRelativeProjection A)).mp
    rw [← Category.assoc, hE, Category.assoc,
      integralPairInclusion_projection B (Set.range f), hfπ]
    simp only [integralSubspaceChains, ← Category.assoc, ← CategoryTheory.Functor.map_comp]
    rfl
  let : IsIso (homologyMap (integralPairInclusion B (Set.range f)) n) :=
    integral_interior_cover_excision B (Set.range f) hf.isOpen_range hcover n
  rw [← hfactor, homologyMap_comp]
  infer_instance

/-- A closed support inside the range of an open embedding supplies the
interior cover, even when the relative subset is larger than its exterior.
Source: Hatcher, Theorem 2.20, p. 119, and M53 derivation 11. -/
theorem integralRelativeMap_isIso_of_closed_support
    (f : C(X, Y)) (hf : IsOpenEmbedding f) {A : Set X} {B K : Set Y}
    (hAB : ∀ x, x ∈ A ↔ f x ∈ B) (hK : IsClosed K)
    (hKr : K ⊆ Set.range f) (hKB : Kᶜ ⊆ B) (n : Nat) :
    IsIso (homologyMap (integralRelativeMap f (fun x hx => (hAB x).mp hx)) n) := by
  apply integralRelativeMap_isIso_of_isOpenEmbedding f hf hAB _ n
  apply Set.eq_univ_iff_forall.mpr
  intro y
  by_cases hy : y ∈ K
  · exact Or.inr (hKr hy)
  · exact Or.inl ((interior_maximal hKB hK.isOpen_compl) hy)

end PoincareMT.Topology.EmbeddedSphere
