import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.CompactSupport.IntegralCompactCohomology
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.IntegralCohomologyExcision
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Relative.IntegralChartSupport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits HomologicalComplex TopologicalSpace Set

universe u

namespace Poincare.Topology

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

@[reassoc]
theorem integralRelativeMap_comp (f : C(X, Y)) (g : C(Y, Z))
    {A : Set X} {B : Set Y} {D : Set Z}
    (hf : MapsTo f A B) (hg : MapsTo g B D) :
    integralRelativeMap f hf ≫ integralRelativeMap g hg =
      integralRelativeMap (g.comp f) (hg.comp hf) := by
  apply (cancel_epi (integralRelativeProjection A)).mp
  rw [← Category.assoc, integralRelativeMap_projection, Category.assoc,
    integralRelativeMap_projection, ← Category.assoc, ← Functor.map_comp,
    integralRelativeMap_projection]
  rfl

def integralSupportEmbeddingChains (f : C(X, Y)) (hf : Function.Injective f) (K : Set X) :
    integralSupportChains K ⟶ integralSupportChains (f '' K) :=
  integralRelativeMap f (by
    intro x hx
    rintro ⟨y, hy, hxy⟩
    exact hx (hf hxy ▸ hy))

@[reassoc (attr := simp)]
theorem integralSupportEmbeddingChains_projection
    (f : C(X, Y)) (hf : Function.Injective f) (K : Set X) :
    integralRelativeProjection Kᶜ ≫ integralSupportEmbeddingChains f hf K =
      integralChainsFunctor.map (TopCat.ofHom f) ≫ integralRelativeProjection (f '' K)ᶜ :=
  integralRelativeMap_projection _ _

theorem integralSupportEmbeddingChains_naturality
    (f : C(X, Y)) (hf : Function.Injective f) {K L : Set X} (hKL : K ⊆ L) :
    integralSupportEmbeddingChains f hf L ≫ integralSupportRestriction (image_mono hKL) =
      integralSupportRestriction hKL ≫ integralSupportEmbeddingChains f hf K := by
  apply (cancel_epi (integralRelativeProjection Lᶜ)).mp
  rw [← Category.assoc, integralSupportEmbeddingChains_projection, Category.assoc,
    integralSupportRestriction_projection, ← Category.assoc,
    integralSupportRestriction_projection, integralSupportEmbeddingChains_projection]

theorem integralSupportEmbeddingChains_dual_isIso [T2Space Y]
    (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f)
    (K : Compacts X) (q : Nat) :
    IsIso (homologyMap (integralDualMap
      (integralSupportEmbeddingChains f hf.injective (K : Set X))) q) := by
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
  have hi : IsIso (homologyMap (integralDualMap i) q) := by
    apply integral_open_cover_cohomology_excision (f '' (K : Set X))ᶜ R
      (K.isCompact.image f.continuous).isClosed.isOpen_compl hf.isOpen_range ?_ q
    apply Set.eq_univ_iff_forall.mpr
    intro y
    by_cases hy : y ∈ f '' (K : Set X)
    · exact Or.inr (Set.image_subset_range _ _ hy)
    · exact Or.inl hy
  let := hi
  rw [heq, integralDualMap_comp, homologyMap_comp]
  have : IsIso (homologyMap (integralDualMap E.hom) q) := by
    change IsIso ((homologyFunctor (ModuleCat.{u} Int) (ComplexShape.up Nat) q).map
      (integralDualIso E).hom)
    infer_instance
  infer_instance

def integralSupportOpenEmbeddingCohomologyIso [T2Space Y]
    (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f)
    (K : Compacts X) (q : Nat) :
    integralSupportCohomology (f '' (K : Set X)) q ≅
      integralSupportCohomology (K : Set X) q :=
  letI := integralSupportEmbeddingChains_dual_isIso f hf K q
  asIso (homologyMap (integralDualMap
    (integralSupportEmbeddingChains f hf.injective (K : Set X))) q)

@[reassoc]
theorem integralSupportOpenEmbeddingCohomologyIso_naturality [T2Space Y]
    (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f)
    {K L : Compacts X} (hKL : K ≤ L) (q : Nat) :
    integralSupportCohomologyPushforward (image_mono hKL) q ≫
        (integralSupportOpenEmbeddingCohomologyIso f hf L q).hom =
      (integralSupportOpenEmbeddingCohomologyIso f hf K q).hom ≫
        integralSupportCohomologyPushforward hKL q := by
  change homologyMap (integralDualMap (integralSupportRestriction (image_mono hKL))) q ≫
      homologyMap (integralDualMap (integralSupportEmbeddingChains f hf.injective L)) q =
    homologyMap (integralDualMap (integralSupportEmbeddingChains f hf.injective K)) q ≫
      homologyMap (integralDualMap (integralSupportRestriction hKL)) q
  rw [← homologyMap_comp, ← homologyMap_comp, ← integralDualMap_comp,
    ← integralDualMap_comp, integralSupportEmbeddingChains_naturality f hf.injective hKL]

def integralCompactSupportCohomologyOpenMap [T2Space Y]
    (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f) (q : Nat) :
    integralCompactSupportCohomology X q ⟶ integralCompactSupportCohomology Y q :=
  integralCompactSupportCohomologyDesc q _
    (fun K => (integralSupportOpenEmbeddingCohomologyIso f hf K q).inv ≫
      integralCompactSupportCohomologyClass (K.map f f.continuous) q) (by
        intro K L hKL
        apply (cancel_epi (integralSupportOpenEmbeddingCohomologyIso f hf K q).hom).mp
        rw [← Category.assoc, ← integralSupportOpenEmbeddingCohomologyIso_naturality]
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
        exact integralCompactSupportCohomologyClass_pushforward
          (show K.map f f.continuous ≤ L.map f f.continuous from image_mono hKL) q)

@[reassoc (attr := simp)]
theorem integralCompactSupportCohomologyOpenMap_class [T2Space Y]
    (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f)
    (K : Compacts X) (q : Nat) :
    integralCompactSupportCohomologyClass K q ≫ integralCompactSupportCohomologyOpenMap f hf q =
      (integralSupportOpenEmbeddingCohomologyIso f hf K q).inv ≫
        integralCompactSupportCohomologyClass (K.map f f.continuous) q :=
  integralCompactSupportCohomologyClass_desc _ _ _ _ _

@[reassoc (attr := simp)]
theorem integralCompactSupportCohomologyOpenMap_pullback_class [T2Space Y]
    (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f)
    (K : Compacts X) (q : Nat) :
    (integralSupportOpenEmbeddingCohomologyIso f hf K q).hom ≫
        integralCompactSupportCohomologyClass K q ≫
          integralCompactSupportCohomologyOpenMap f hf q =
      integralCompactSupportCohomologyClass (K.map f f.continuous) q := by
  rw [integralCompactSupportCohomologyOpenMap_class, Iso.hom_inv_id_assoc]

theorem integralSupportEmbeddingChains_comp
    (f : C(X, Y)) (g : C(Y, Z)) (hf : Function.Injective f) (hg : Function.Injective g)
    (K : Set X) (himage : g '' (f '' K) ⊆ (g.comp f) '' K) :
    integralSupportEmbeddingChains f hf K ≫ integralSupportEmbeddingChains g hg (f '' K) =
      integralSupportEmbeddingChains (g.comp f) (hg.comp hf) K ≫
        integralSupportRestriction himage := by
  apply (cancel_epi (integralRelativeProjection Kᶜ)).mp
  simp only [integralSupportEmbeddingChains_projection_assoc,
    integralSupportEmbeddingChains_projection, integralSupportRestriction_projection]
  rw [← Category.assoc, ← Functor.map_comp]
  rfl

@[reassoc]
theorem integralCompactSupportCohomologyOpenMap_comp [T2Space Y] [T2Space Z]
    (f : C(X, Y)) (g : C(Y, Z))
    (hf : _root_.Topology.IsOpenEmbedding f) (hg : _root_.Topology.IsOpenEmbedding g)
    (q : Nat) :
    integralCompactSupportCohomologyOpenMap f hf q ≫
        integralCompactSupportCohomologyOpenMap g hg q =
      integralCompactSupportCohomologyOpenMap (g.comp f) (hg.comp hf) q := by
  apply integralCompactSupportCohomology_hom_ext q
  intro K
  let L := K.map f f.continuous
  let P := L.map g g.continuous
  let Q := K.map (g.comp f) (g.comp f).continuous
  have hPQ : P ≤ Q := by
    rintro _ ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  let ef := integralSupportOpenEmbeddingCohomologyIso f hf K q
  let eg := integralSupportOpenEmbeddingCohomologyIso g hg L q
  let ec := integralSupportOpenEmbeddingCohomologyIso (g.comp f) (hg.comp hf) K q
  have hc : integralSupportCohomologyPushforward hPQ q ≫ ec.hom = eg.hom ≫ ef.hom := by
    change homologyMap (integralDualMap (integralSupportRestriction hPQ)) q ≫
        homologyMap (integralDualMap
          (integralSupportEmbeddingChains (g.comp f) (hg.injective.comp hf.injective) K)) q =
      homologyMap (integralDualMap (integralSupportEmbeddingChains g hg.injective (f '' (K :
        Set X)))) q ≫
        homologyMap (integralDualMap (integralSupportEmbeddingChains f hf.injective K)) q
    rw [← homologyMap_comp, ← homologyMap_comp, ← integralDualMap_comp,
      ← integralDualMap_comp, integralSupportEmbeddingChains_comp f g hf.injective
        hg.injective K hPQ]
  apply (cancel_epi (eg.hom ≫ ef.hom)).mp
  dsimp only [ef, eg, L]
  simp only [Category.assoc, integralCompactSupportCohomologyOpenMap_pullback_class_assoc,
    integralCompactSupportCohomologyOpenMap_pullback_class]
  change integralCompactSupportCohomologyClass P q =
    eg.hom ≫ ef.hom ≫ integralCompactSupportCohomologyClass K q ≫
      integralCompactSupportCohomologyOpenMap (g.comp f) (hg.comp hf) q
  rw [← Category.assoc eg.hom, ← hc, Category.assoc,
    integralCompactSupportCohomologyOpenMap_pullback_class]
  exact (integralCompactSupportCohomologyClass_pushforward hPQ q).symm

@[simp]
theorem integralCompactSupportCohomologyOpenMap_id [T2Space X] (q : Nat) :
    integralCompactSupportCohomologyOpenMap (ContinuousMap.id X)
      _root_.Topology.IsOpenEmbedding.id q = 𝟙 (integralCompactSupportCohomology X q) := by
  apply integralCompactSupportCohomology_hom_ext q
  intro K
  let f := ContinuousMap.id X
  have hIK : f '' (K : Set X) ⊆ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hchain : integralSupportEmbeddingChains f Function.injective_id (K : Set X) =
      integralSupportRestriction hIK := by
    apply (cancel_epi (integralRelativeProjection (K : Set X)ᶜ)).mp
    rw [integralSupportEmbeddingChains_projection, integralSupportRestriction_projection]
    change integralChainsFunctor.map (𝟙 (TopCat.of X)) ≫ _ = _
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  let e := integralSupportOpenEmbeddingCohomologyIso f _root_.Topology.IsOpenEmbedding.id K q
  have he : e.hom = integralSupportCohomologyPushforward hIK q := by
    change homologyMap (integralDualMap
      (integralSupportEmbeddingChains f Function.injective_id (K : Set X))) q = _
    rw [hchain]
    rfl
  apply (cancel_epi e.hom).mp
  rw [integralCompactSupportCohomologyOpenMap_pullback_class, Category.comp_id, he]
  exact (integralCompactSupportCohomologyClass_pushforward
    (show K.map f f.continuous ≤ K from hIK) q).symm

end Poincare.Topology
