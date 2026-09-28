import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportRangeMap



set_option autoImplicit false

noncomputable section

open CategoryTheory Limits TopologicalSpace Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {I W : Type u} [TopologicalSpace I] [TopologicalSpace W] [T2Space W]

theorem integralCompactSupportCohomologyRangeMap_eq_zero_iff
    (f : C(I, W)) (hf : _root_.Topology.IsOpenEmbedding f)
    (R : Compacts W) (hR : (R : Set W) ⊆ Set.range f) (q : Nat)
    (c : integralSupportCohomology (R : Set W) q) :
    integralCompactSupportCohomologyRangeMap f hf R hR q c = 0 ↔
      ∃ (S : Compacts I) (hRS : (R : Set W) ⊆ f '' (S : Set I)),
        integralSupportCohomologyPushforward hRS q c = 0 := by
  constructor
  · intro hc
    let S := integralCompactSupportRangePreimage f hf R hR
    have hRS : (R : Set W) ⊆ f '' (S : Set I) :=
      (integralCompactSupportRangePreimage_image_eq f hf R hR).symm.le
    change integralCompactSupportCohomologyClass S q
      ((integralSupportOpenEmbeddingCohomologyIso f hf S q).hom
        (integralSupportCohomologyPushforward hRS q c)) = 0 at hc
    obtain ⟨P, hSP, hP⟩ := (integralCompactSupportCohomologyClass_eq_zero_iff _).mp hc
    refine ⟨P, hRS.trans (image_mono hSP), ?_⟩
    let e := integralSupportOpenEmbeddingCohomologyIso f hf P q
    have he := congrArg (fun k => k.hom (integralSupportCohomologyPushforward hRS q c))
      (integralSupportOpenEmbeddingCohomologyIso_naturality f hf hSP q)
    have hz : e.hom
        (integralSupportCohomologyPushforward (hRS.trans (image_mono hSP)) q c) = 0 := by
      rw [← integralSupportCohomologyPushforward_comp hRS (image_mono hSP) q]
      exact he.trans hP
    apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
    simpa only [map_zero] using hz
  · rintro ⟨S, hRS, hc⟩
    have hn := congrArg (fun k => k.hom c)
      (integralCompactSupportCohomologyRangeMap_naturality f hf
        (show R ≤ S.map f f.continuous from hRS) hR (image_subset_range _ _) q)
    exact hn.symm.trans
      ((congrArg (integralCompactSupportCohomologyRangeMap f hf
        (S.map f f.continuous) (image_subset_range _ _) q).hom hc).trans (map_zero _))

end PoincareConjecture.Proofs.M02.Topology
