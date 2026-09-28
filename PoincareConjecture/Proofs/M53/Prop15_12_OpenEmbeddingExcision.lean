import PoincareConjecture.Proofs.M53.Prop15_12_Excision











set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex Topology
open PoincareConjecture.Proofs.M02.Topology

universe u

namespace PoincareConjecture.Proofs.M53

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]




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

end PoincareConjecture.Proofs.M53
