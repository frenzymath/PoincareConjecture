import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportRangeMapTransport



set_option autoImplicit false

noncomputable section

open CategoryTheory Limits TopologicalSpace Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {I Y W : Type u} [TopologicalSpace I] [TopologicalSpace Y] [TopologicalSpace W]

theorem exists_integralCompactSupportCohomology_range_representative
    [T2Space W] (f : C(I, W)) (hf : _root_.Topology.IsOpenEmbedding f) (q : Nat)
    (z : integralCompactSupportCohomology I q) :
    ∃ (S : Compacts I) (c : integralSupportCohomology (f '' (S : Set I)) q),
      integralCompactSupportCohomologyRangeMap f hf (S.map f f.continuous)
        (image_subset_range _ _) q c = z := by
  obtain ⟨S, a, ha⟩ := exists_integralCompactSupportCohomology_representative q z
  let e := integralSupportOpenEmbeddingCohomologyIso f hf S q
  refine ⟨S, e.inv a, ?_⟩
  have he := congrArg (fun k => k.hom (e.inv a))
    (integralCompactSupportCohomologyRangeMap_image f hf S (image_subset_range _ _) q)
  have hcancel : e.hom (e.inv a) = a :=
    congrArg (fun k => k.hom a) e.inv_hom_id
  exact he.trans ((congrArg (integralCompactSupportCohomologyClass S q).hom hcancel).trans ha)

theorem exists_integralCompactSupportCohomology_pushforward_zero_of_pullback_class_zero
    [T2Space W] (g : C(Y, W)) (hg : _root_.Topology.IsOpenEmbedding g)
    (R : Compacts W) (A : Compacts Y)
    (hRA : (R : Set W) ⊆ g '' (A : Set Y)) (q : Nat)
    (c : integralSupportCohomology (R : Set W) q)
    (hc : integralCompactSupportCohomologyClass A q
      ((integralSupportOpenEmbeddingCohomologyIso g hg A q).hom
        (integralSupportCohomologyPushforward hRA q c)) = 0) :
    ∃ (A' : Compacts Y) (hAA' : A ≤ A'),
      integralSupportCohomologyPushforward (hRA.trans (image_mono hAA')) q c = 0 := by
  obtain ⟨A', hAA', hzero⟩ := (integralCompactSupportCohomologyClass_eq_zero_iff _).mp hc
  refine ⟨A', hAA', ?_⟩
  let e := integralSupportOpenEmbeddingCohomologyIso g hg A' q
  have hn := congrArg (fun k => k.hom (integralSupportCohomologyPushforward hRA q c))
    (integralSupportOpenEmbeddingCohomologyIso_naturality g hg hAA' q)
  have hcomp := congrArg (fun k => k.hom c)
    (integralSupportCohomologyPushforward_comp hRA (image_mono hAA') q)
  have hz : e.hom
      (integralSupportCohomologyPushforward (hRA.trans (image_mono hAA')) q c) = 0 :=
    (congrArg e.hom.hom hcomp.symm).trans (hn.trans hzero)
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  simpa only [map_zero] using hz

theorem exists_integralCompactSupportCohomology_pushforward_zero_of_openMap_rangeMap_zero
    [T2Space Y] [T2Space W]
    (f : C(I, Y)) (g : C(Y, W)) (t : C(I, W))
    (hf : _root_.Topology.IsOpenEmbedding f) (hg : _root_.Topology.IsOpenEmbedding g)
    (ht : _root_.Topology.IsOpenEmbedding t) (heq : t = g.comp f)
    (R : Compacts W) (hR : (R : Set W) ⊆ Set.range t)
    (A : Compacts Y) (hRA : (R : Set W) ⊆ g '' (A : Set Y)) (q : Nat)
    (c : integralSupportCohomology (R : Set W) q)
    (hc : integralCompactSupportCohomologyOpenMap f hf q
      (integralCompactSupportCohomologyRangeMap t ht R hR q c) = 0) :
    ∃ (A' : Compacts Y) (hAA' : A ≤ A'),
      integralSupportCohomologyPushforward (hRA.trans (image_mono hAA')) q c = 0 := by
  have he := congrArg (fun k => k.hom c)
    (integralCompactSupportCohomologyRangeMap_openMap f g t hf hg ht heq R hR A hRA q)
  exact exists_integralCompactSupportCohomology_pushforward_zero_of_pullback_class_zero
    g hg R A hRA q c (he.symm.trans hc)

end PoincareConjecture.Proofs.M02.Topology
