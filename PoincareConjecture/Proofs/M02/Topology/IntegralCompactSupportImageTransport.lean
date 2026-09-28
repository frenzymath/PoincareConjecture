import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportNestedTransport








set_option autoImplicit false

noncomputable section

open CategoryTheory Limits TopologicalSpace Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {I Y W : Type u} [TopologicalSpace I] [TopologicalSpace Y] [TopologicalSpace W]

theorem integralCompactSupportCohomologyOpenMap_class_of_image_support
    [T2Space Y] [T2Space W]
    (f : C(I, Y)) (g : C(Y, W))
    (hf : _root_.Topology.IsOpenEmbedding f) (hg : _root_.Topology.IsOpenEmbedding g)
    (S : Compacts I) (R : Compacts W) (A : Compacts Y)
    (hSR : S.map (g.comp f) (g.comp f).continuous = R)
    (hRS : (R : Set W) ⊆ (g.comp f) '' (S : Set I))
    (hRA : (R : Set W) ⊆ g '' (A : Set Y))
    (q : Nat) (c : integralSupportCohomology (R : Set W) q) :
    (integralCompactSupportCohomologyClass S q ≫
        integralCompactSupportCohomologyOpenMap f hf q)
      ((integralSupportOpenEmbeddingCohomologyIso (g.comp f) (hg.comp hf) S q).hom
        (integralSupportCohomologyPushforward hRS q c)) =
      integralCompactSupportCohomologyClass A q
        ((integralSupportOpenEmbeddingCohomologyIso g hg A q).hom
          (integralSupportCohomologyPushforward hRA q c)) := by
  have hSA : S.map f f.continuous ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    have hxR : (g.comp f) x ∈ (R : Set W) := by
      rw [← hSR]
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, heq⟩ := hRA hxR
    exact hg.injective heq ▸ hy
  let e := integralSupportOpenEmbeddingCohomologyIso g hg A q
  have hinv : e.inv (e.hom (integralSupportCohomologyPushforward hRA q c)) =
      integralSupportCohomologyPushforward hRA q c := by
    change (e.hom ≫ e.inv) _ = _
    rw [e.hom_inv_id]
    rfl
  apply integralCompactSupportCohomologyOpenMap_class_eq_of_nested_pushforward_eq
    f g hf hg hSA (le_refl A) q
  change (integralSupportCohomologyPushforward hRS q ≫
      integralSupportCohomologyPushforward _ q) c =
    integralSupportCohomologyPushforward (image_mono (le_refl A)) q
      (e.inv (e.hom (integralSupportCohomologyPushforward hRA q c)))
  rw [integralSupportCohomologyPushforward_comp, hinv,
    integralSupportCohomologyPushforward_refl]
  rfl

theorem integralCompactSupportCohomologyOpenMap_class_of_composite_support
    [T2Space Y] [T2Space W]
    (f : C(I, Y)) (g : C(Y, W)) (t : C(I, W))
    (hf : _root_.Topology.IsOpenEmbedding f) (hg : _root_.Topology.IsOpenEmbedding g)
    (ht : _root_.Topology.IsOpenEmbedding t) (heq : t = g.comp f)
    (S : Compacts I) (R : Compacts W) (A : Compacts Y)
    (hSR : S.map t t.continuous = R)
    (hRS : (R : Set W) ⊆ t '' (S : Set I))
    (hRA : (R : Set W) ⊆ g '' (A : Set Y))
    (q : Nat) (c : integralSupportCohomology (R : Set W) q) :
    (integralCompactSupportCohomologyClass S q ≫
        integralCompactSupportCohomologyOpenMap f hf q)
      ((integralSupportOpenEmbeddingCohomologyIso t ht S q).hom
        (integralSupportCohomologyPushforward hRS q c)) =
      integralCompactSupportCohomologyClass A q
        ((integralSupportOpenEmbeddingCohomologyIso g hg A q).hom
          (integralSupportCohomologyPushforward hRA q c)) := by
  subst t
  exact integralCompactSupportCohomologyOpenMap_class_of_image_support
    f g hf hg S R A hSR hRS hRA q c

end PoincareConjecture.Proofs.M02.Topology
