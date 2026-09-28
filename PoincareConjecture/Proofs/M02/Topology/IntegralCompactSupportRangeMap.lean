import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportImageTransport









set_option autoImplicit false

noncomputable section

open CategoryTheory Limits TopologicalSpace Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {I W : Type u} [TopologicalSpace I] [TopologicalSpace W]

def integralCompactSupportRangePreimage
    (f : C(I, W)) (hf : _root_.Topology.IsOpenEmbedding f)
    (R : Compacts W) (hR : (R : Set W) ⊆ Set.range f) : Compacts I :=
  ⟨f ⁻¹' (R : Set W), hf.isEmbedding.isCompact_preimage' R.isCompact hR⟩

theorem integralCompactSupportRangePreimage_image_eq
    (f : C(I, W)) (hf : _root_.Topology.IsOpenEmbedding f)
    (R : Compacts W) (hR : (R : Set W) ⊆ Set.range f) :
    f '' (integralCompactSupportRangePreimage f hf R hR : Set I) = (R : Set W) := by
  exact image_preimage_eq_of_subset hR

theorem integralCompactSupportRangePreimage_mono
    (f : C(I, W)) (hf : _root_.Topology.IsOpenEmbedding f)
    {R R' : Compacts W} (hRR' : R ≤ R')
    (hR : (R : Set W) ⊆ Set.range f)
    (hR' : (R' : Set W) ⊆ Set.range f) :
    integralCompactSupportRangePreimage f hf R hR ≤
      integralCompactSupportRangePreimage f hf R' hR' := by
  intro x hx
  exact hRR' hx

def integralCompactSupportCohomologyRangeMap [T2Space W]
    (f : C(I, W)) (hf : _root_.Topology.IsOpenEmbedding f)
    (R : Compacts W) (hR : (R : Set W) ⊆ Set.range f) (q : Nat) :
    integralSupportCohomology (R : Set W) q ⟶
      integralCompactSupportCohomology I q :=
  let S := integralCompactSupportRangePreimage f hf R hR
  integralSupportCohomologyPushforward
      (show (R : Set W) ⊆ f '' (S : Set I) from
        (integralCompactSupportRangePreimage_image_eq f hf R hR).symm.le) q ≫
    (integralSupportOpenEmbeddingCohomologyIso f hf S q).hom ≫
      integralCompactSupportCohomologyClass S q

theorem integralCompactSupportCohomologyRangeMap_naturality [T2Space W]
    (f : C(I, W)) (hf : _root_.Topology.IsOpenEmbedding f)
    {R R' : Compacts W} (hRR' : R ≤ R')
    (hR : (R : Set W) ⊆ Set.range f)
    (hR' : (R' : Set W) ⊆ Set.range f) (q : Nat) :
    integralSupportCohomologyPushforward hRR' q ≫
        integralCompactSupportCohomologyRangeMap f hf R' hR' q =
      integralCompactSupportCohomologyRangeMap f hf R hR q := by
  let S := integralCompactSupportRangePreimage f hf R hR
  let S' := integralCompactSupportRangePreimage f hf R' hR'
  have hSS' : S ≤ S' :=
    integralCompactSupportRangePreimage_mono f hf hRR' hR hR'
  have hSS's : (S : Set I) ⊆ (S' : Set I) := hSS'
  have hRi : (R : Set W) ⊆ f '' (S : Set I) :=
    (integralCompactSupportRangePreimage_image_eq f hf R hR).symm.le
  have hR'i : (R' : Set W) ⊆ f '' (S' : Set I) :=
    (integralCompactSupportRangePreimage_image_eq f hf R' hR').symm.le
  have hRR's : (R : Set W) ⊆ (R' : Set W) := hRR'
  change integralSupportCohomologyPushforward hRR's q ≫
      integralSupportCohomologyPushforward hR'i q ≫
        (integralSupportOpenEmbeddingCohomologyIso f hf S' q).hom ≫
          integralCompactSupportCohomologyClass S' q =
    integralSupportCohomologyPushforward hRi q ≫
      (integralSupportOpenEmbeddingCohomologyIso f hf S q).hom ≫
        integralCompactSupportCohomologyClass S q
  have hleft : integralSupportCohomologyPushforward hRR's q ≫
      integralSupportCohomologyPushforward hR'i q =
      integralSupportCohomologyPushforward
        (hRi.trans (image_mono hSS's)) q := by
    rw [integralSupportCohomologyPushforward_comp]
  have hclass := integralCompactSupportCohomologyClass_pushforward hSS' q
  rw [← Category.assoc, hleft]
  rw [← integralSupportCohomologyPushforward_comp hRi (image_mono hSS's) q]
  rw [Category.assoc, integralSupportOpenEmbeddingCohomologyIso_naturality_assoc f hf hSS' q,
    hclass]

end PoincareConjecture.Proofs.M02.Topology
