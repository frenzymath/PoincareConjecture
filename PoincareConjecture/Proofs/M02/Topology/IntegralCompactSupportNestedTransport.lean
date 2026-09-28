import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportClassTransport









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits HomologicalComplex TopologicalSpace Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem integralSupportOpenEmbeddingCohomologyIso_comp [T2Space Y] [T2Space Z]
    (f : C(X, Y)) (g : C(Y, Z))
    (hf : _root_.Topology.IsOpenEmbedding f) (hg : _root_.Topology.IsOpenEmbedding g)
    (K : Compacts X) (q : Nat)
    (himage : g '' (f '' (K : Set X)) ⊆ (g.comp f) '' (K : Set X)) :
    integralSupportCohomologyPushforward himage q ≫
        (integralSupportOpenEmbeddingCohomologyIso (g.comp f) (hg.comp hf) K q).hom =
      (integralSupportOpenEmbeddingCohomologyIso g hg (K.map f f.continuous) q).hom ≫
        (integralSupportOpenEmbeddingCohomologyIso f hf K q).hom := by
  change homologyMap (integralDualMap (integralSupportRestriction himage)) q ≫
      homologyMap (integralDualMap
        (integralSupportEmbeddingChains (g.comp f) (hg.injective.comp hf.injective) K)) q =
    homologyMap (integralDualMap (integralSupportEmbeddingChains g hg.injective (f '' (K :
      Set X)))) q ≫
      homologyMap (integralDualMap (integralSupportEmbeddingChains f hf.injective K)) q
  rw [← homologyMap_comp, ← homologyMap_comp, ← integralDualMap_comp,
    ← integralDualMap_comp, integralSupportEmbeddingChains_comp f g hf.injective hg.injective
      K himage]

theorem integralCompactSupportCohomologyOpenMap_class_eq_of_nested_pushforward_eq
    [T2Space Y] [T2Space Z] (f : C(X, Y)) (g : C(Y, Z))
    (hf : _root_.Topology.IsOpenEmbedding f) (hg : _root_.Topology.IsOpenEmbedding g)
    {S : Compacts X} {A P : Compacts Y}
    (hSP : S.map f f.continuous ≤ P) (hAP : A ≤ P) (q : Nat)
    (c : integralSupportCohomology ((g.comp f) '' (S : Set X)) q)
    (a : integralSupportCohomology (A : Set Y) q)
    (h : integralSupportCohomologyPushforward
        (show (g.comp f) '' (S : Set X) ⊆ g '' (P : Set Y) from by
          rintro _ ⟨x, hx, rfl⟩
          exact ⟨f x, hSP ⟨x, hx, rfl⟩, rfl⟩) q c =
      integralSupportCohomologyPushforward (image_mono hAP) q
        ((integralSupportOpenEmbeddingCohomologyIso g hg A q).inv a)) :
    (integralCompactSupportCohomologyClass S q ≫
        integralCompactSupportCohomologyOpenMap f hf q)
        ((integralSupportOpenEmbeddingCohomologyIso (g.comp f) (hg.comp hf) S q).hom c) =
      integralCompactSupportCohomologyClass A q a := by
  let T := S.map f f.continuous
  let ef := integralSupportOpenEmbeddingCohomologyIso f hf S q
  let eg := integralSupportOpenEmbeddingCohomologyIso g hg T q
  let ec := integralSupportOpenEmbeddingCohomologyIso (g.comp f) (hg.comp hf) S q
  have hCG : (g.comp f) '' (S : Set X) ⊆ g '' (T : Set Y) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩
  have hGC : g '' (T : Set Y) ⊆ (g.comp f) '' (S : Set X) := by
    rintro _ ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  let d := integralSupportCohomologyPushforward hCG q c
  have hdc : integralSupportCohomologyPushforward hGC q d = c := by
    change (integralSupportCohomologyPushforward hCG q ≫
      integralSupportCohomologyPushforward hGC q) c = c
    rw [integralSupportCohomologyPushforward_comp]
    have he : integralSupportCohomologyPushforward (hCG.trans hGC) q =
        𝟙 (integralSupportCohomology ((g.comp f) '' (S : Set X)) q) :=
      integralSupportCohomologyPushforward_refl _ q
    rw [he]
    rfl
  have hec : ec.hom c = ef.hom (eg.hom d) := by
    have he := congrArg (fun k => k d)
      (integralSupportOpenEmbeddingCohomologyIso_comp f g hf hg S q hGC)
    change ec.hom (integralSupportCohomologyPushforward hGC q d) =
      ef.hom (eg.hom d) at he
    rwa [hdc] at he
  have hmap :
      (integralCompactSupportCohomologyClass S q ≫
          integralCompactSupportCohomologyOpenMap f hf q) (ec.hom c) =
        integralCompactSupportCohomologyClass T q (eg.hom d) := by
    rw [hec]
    exact congrArg (fun k => k (eg.hom d))
      (integralCompactSupportCohomologyOpenMap_pullback_class f hf S q)
  have hd : integralSupportCohomologyPushforward (image_mono hSP) q d =
      integralSupportCohomologyPushforward (image_mono hAP) q
        ((integralSupportOpenEmbeddingCohomologyIso g hg A q).inv a) := by
    change (integralSupportCohomologyPushforward hCG q ≫
      integralSupportCohomologyPushforward (image_mono hSP) q) c = _
    rw [integralSupportCohomologyPushforward_comp]
    exact h
  have hclass := integralCompactSupportCohomologyClass_pullback_eq_of_pushforward_eq
    g hg hSP hAP q d ((integralSupportOpenEmbeddingCohomologyIso g hg A q).inv a) hd
  have ha : (integralSupportOpenEmbeddingCohomologyIso g hg A q).hom
      ((integralSupportOpenEmbeddingCohomologyIso g hg A q).inv a) = a := by
    change ((integralSupportOpenEmbeddingCohomologyIso g hg A q).inv ≫
      (integralSupportOpenEmbeddingCohomologyIso g hg A q).hom) a = a
    rw [Iso.inv_hom_id]
    rfl
  rw [ha] at hclass
  exact hmap.trans hclass

end PoincareConjecture.Proofs.M02.Topology
