import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.CompactSupport.Transport.IntegralCompactSupportRangeMapZero


set_option autoImplicit false

noncomputable section

open CategoryTheory Limits TopologicalSpace Set

universe u

namespace Poincare.Topology

variable {I Y W : Type u} [TopologicalSpace I] [TopologicalSpace Y] [TopologicalSpace W]

theorem integralCompactSupportCohomologyRangeMap_eq_of_subset_image [T2Space W]
    (f : C(I, W)) (hf : _root_.Topology.IsOpenEmbedding f)
    (R : Compacts W) (hR : (R : Set W) ⊆ Set.range f)
    (S : Compacts I) (hRS : (R : Set W) ⊆ f '' (S : Set I)) (q : Nat) :
    integralCompactSupportCohomologyRangeMap f hf R hR q =
      integralSupportCohomologyPushforward hRS q ≫
        (integralSupportOpenEmbeddingCohomologyIso f hf S q).hom ≫
          integralCompactSupportCohomologyClass S q := by
  let T := integralCompactSupportRangePreimage f hf R hR
  have hRT : (R : Set W) ⊆ f '' (T : Set I) :=
    (integralCompactSupportRangePreimage_image_eq f hf R hR).symm.le
  have hTS : T ≤ S := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hRS hx
    exact hf.injective hxy ▸ hy
  change integralSupportCohomologyPushforward hRT q ≫
      (integralSupportOpenEmbeddingCohomologyIso f hf T q).hom ≫
        integralCompactSupportCohomologyClass T q = _
  rw [← integralCompactSupportCohomologyClass_pushforward hTS q,
    ← integralSupportOpenEmbeddingCohomologyIso_naturality_assoc f hf hTS q,
    ← Category.assoc,
    integralSupportCohomologyPushforward_comp hRT (image_mono hTS) q]

theorem integralCompactSupportCohomologyRangeMap_image [T2Space W]
    (f : C(I, W)) (hf : _root_.Topology.IsOpenEmbedding f)
    (S : Compacts I) (hS : (S.map f f.continuous : Set W) ⊆ Set.range f) (q : Nat) :
    integralCompactSupportCohomologyRangeMap f hf (S.map f f.continuous) hS q =
      (integralSupportOpenEmbeddingCohomologyIso f hf S q).hom ≫
        integralCompactSupportCohomologyClass S q := by
  have hS' : (S.map f f.continuous : Set W) ⊆ f '' (S : Set I) := Subset.refl _
  rw [integralCompactSupportCohomologyRangeMap_eq_of_subset_image f hf
    (S.map f f.continuous) hS S hS' q]
  have hid : integralSupportCohomologyPushforward hS' q =
      𝟙 (integralSupportCohomology (f '' (S : Set I)) q) :=
    integralSupportCohomologyPushforward_refl (f '' (S : Set I)) q
  exact (congrArg (fun k => k ≫
    (integralSupportOpenEmbeddingCohomologyIso f hf S q).hom ≫
      integralCompactSupportCohomologyClass S q) hid).trans (Category.id_comp _)

theorem integralCompactSupportCohomologyRangeMap_openMap
    [T2Space Y] [T2Space W]
    (f : C(I, Y)) (g : C(Y, W)) (t : C(I, W))
    (hf : _root_.Topology.IsOpenEmbedding f) (hg : _root_.Topology.IsOpenEmbedding g)
    (ht : _root_.Topology.IsOpenEmbedding t) (heq : t = g.comp f)
    (R : Compacts W) (hR : (R : Set W) ⊆ Set.range t)
    (A : Compacts Y) (hRA : (R : Set W) ⊆ g '' (A : Set Y)) (q : Nat) :
    integralCompactSupportCohomologyRangeMap t ht R hR q ≫
        integralCompactSupportCohomologyOpenMap f hf q =
      integralSupportCohomologyPushforward hRA q ≫
        (integralSupportOpenEmbeddingCohomologyIso g hg A q).hom ≫
          integralCompactSupportCohomologyClass A q := by
  let S := integralCompactSupportRangePreimage t ht R hR
  have hRS : (R : Set W) ⊆ t '' (S : Set I) :=
    (integralCompactSupportRangePreimage_image_eq t ht R hR).symm.le
  have hSR : S.map t t.continuous = R := by
    apply Compacts.ext
    exact integralCompactSupportRangePreimage_image_eq t ht R hR
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact integralCompactSupportCohomologyOpenMap_class_of_composite_support
    f g t hf hg ht heq S R A hSR hRS hRA q c

end Poincare.Topology
