import PoincareConjecture.Proofs.M02.Topology.IntegralCompactCohomologyOpenMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits HomologicalComplex TopologicalSpace Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem integralSupportEmbeddingChains_homology_isIso [T2Space Y]
    (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f)
    (K : Compacts X) (q : Nat) :
    IsIso (homologyMap (integralSupportEmbeddingChains f hf.injective (K : Set X)) q) := by
  let R := Set.range f
  let e : X ≃ₜ R := hf.isEmbedding.toHomeomorph
  let A : Set R := (Subtype.val : R → Y) ⁻¹' (f '' (K : Set X))ᶜ
  have hA (x : X) : x ∈ (K : Set X)ᶜ ↔ e x ∈ A := by
    change x ∉ (K : Set X) ↔ f x ∉ f '' (K : Set X)
    constructor
    · intro hx
      rintro ⟨y, hy, hxy⟩
      exact hx (hf.injective hxy ▸ hy)
    · intro hx hxK
      exact hx ⟨x, hxK, rfl⟩
  let E := integralRelativeHomeomorphIso e (K : Set X)ᶜ A hA
  let i := integralOpenSupportMap (f '' (K : Set X)) R
  have heq : integralSupportEmbeddingChains f hf.injective (K : Set X) = E.hom ≫ i := by
    apply (cancel_epi (integralRelativeProjection (K : Set X)ᶜ)).mp
    rw [integralSupportEmbeddingChains_projection, ← Category.assoc,
      integralRelativeHomeomorphIso_projection, Category.assoc]
    change _ = integralChainsFunctor.map (TopCat.ofHom (e : C(X, R))) ≫
      integralRelativeProjection A ≫ integralPairInclusion (f '' (K : Set X))ᶜ R
    rw [integralPairInclusion_projection, ← Category.assoc,
      integralSubspaceChains, ← Functor.map_comp]
    rfl
  have hi : IsIso (homologyMap i q) := by
    apply integralOpenSupportMap_homology_isIso (f '' (K : Set X)) R
      (K.isCompact.image f.continuous).isClosed hf.isOpen_range ?_ q
    exact Set.image_subset_range f (K : Set X)
  let := hi
  rw [heq, homologyMap_comp]
  have hE : IsIso (homologyMap E.hom q) := by
    change IsIso ((homologyFunctor (ModuleCat.{u} Int) (ComplexShape.down Nat) q).map E.hom)
    infer_instance
  infer_instance

end PoincareConjecture.Proofs.M02.Topology
