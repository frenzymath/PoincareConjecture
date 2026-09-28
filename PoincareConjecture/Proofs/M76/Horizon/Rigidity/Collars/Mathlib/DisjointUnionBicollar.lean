import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homeomorph.Lemmas









set_option autoImplicit false
open Set Topology

namespace Poincare.Topology

variable {E F X : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]

def sumSubsetMap (K0 : Set E) (K1 : Set F) : K0 ⊕ K1 → E ⊕ F :=
  Sum.elim (fun x => Sum.inl (x : E)) (fun x => Sum.inr (x : F))

theorem isEmbedding_sumSubsetMap (K0 : Set E) (K1 : Set F) :
    IsEmbedding (sumSubsetMap K0 K1) := by
  have h0 : range (fun x : K0 => (Sum.inl (x : E) : E ⊕ F)) ⊆ range Sum.inl := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  have h1 : range (fun x : K1 => (Sum.inr (x : F) : E ⊕ F)) ⊆ range Sum.inr := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  have hdis : Disjoint (range (Sum.inl : E → E ⊕ F)) (range (Sum.inr : F → E ⊕ F)) := by
    apply disjoint_left.mpr
    rintro _ ⟨x, rfl⟩ ⟨y, h⟩
    cases h
  exact (IsEmbedding.inl.comp IsEmbedding.subtypeVal).sumElim
    (IsEmbedding.inr.comp IsEmbedding.subtypeVal)
    (hdis.mono (closure_minimal h0 isClosed_range_inl) h1)
    (hdis.mono h0 (closure_minimal h1 isClosed_range_inr))

omit [TopologicalSpace E] [TopologicalSpace F] in
theorem range_sumSubsetMap (K0 : Set E) (K1 : Set F) :
    range (sumSubsetMap K0 K1) = Sum.inl '' K0 ∪ Sum.inr '' K1 := by
  ext z
  simp only [sumSubsetMap, Set.Sum.elim_range, mem_union, mem_range, mem_image,
    Subtype.exists, exists_prop]

noncomputable def sumSubsetHomeomorph (K0 : Set E) (K1 : Set F) :
    K0 ⊕ K1 ≃ₜ ↥(Sum.inl '' K0 ∪ Sum.inr '' K1) :=
  (isEmbedding_sumSubsetMap K0 K1).toHomeomorph.trans
    (Homeomorph.setCongr (range_sumSubsetMap K0 K1))

@[simp] theorem sumSubsetHomeomorph_apply_coe (K0 : Set E) (K1 : Set F) (x : K0 ⊕ K1) :
    (sumSubsetHomeomorph K0 K1 x : E ⊕ F) = sumSubsetMap K0 K1 x := rfl

theorem isLocalHomeomorph_sumElim {f : E → X} {g : F → X}
    (hf : IsLocalHomeomorph f) (hg : IsLocalHomeomorph g) :
    IsLocalHomeomorph (Sum.elim f g) := by
  have hleft : IsLocalHomeomorphOn (Sum.elim f g) ((Sum.inl : E → E ⊕ F) '' univ) :=
    (show IsLocalHomeomorphOn ((Sum.elim f g) ∘ Sum.inl) univ from hf.isLocalHomeomorphOn).of_comp_right
      IsOpenEmbedding.inl.isLocalHomeomorph.isLocalHomeomorphOn
  have hright : IsLocalHomeomorphOn (Sum.elim f g) ((Sum.inr : F → E ⊕ F) '' univ) :=
    (show IsLocalHomeomorphOn ((Sum.elim f g) ∘ Sum.inr) univ from hg.isLocalHomeomorphOn).of_comp_right
      IsOpenEmbedding.inr.isLocalHomeomorph.isLocalHomeomorphOn
  intro z
  cases z with
  | inl x => exact hleft _ ⟨x, mem_univ _, rfl⟩
  | inr x => exact hright _ ⟨x, mem_univ _, rfl⟩

theorem isCoveringMap_sumElim_of_compact [T2Space E] [T2Space F] [T2Space X]
    [CompactSpace E] [CompactSpace F] {f : E → X} {g : F → X}
    (hf : IsCoveringMap f) (hg : IsCoveringMap g) : IsCoveringMap (Sum.elim f g) :=
  isLocalHomeomorph_iff_isCoveringMap.mp
    (isLocalHomeomorph_sumElim hf.isLocalHomeomorph hg.isLocalHomeomorph)

variable {T : Type*} [TopologicalSpace T]

def sumBicollarMap (c0 : E × T → X) (c1 : F × T → X) : (E ⊕ F) × T → X :=
  fun z => Sum.elim (fun x => c0 (x, z.2)) (fun x => c1 (x, z.2)) z.1

noncomputable def sumSubsetProdHomeomorph (K0 : Set E) (K1 : Set F) (J : Set T) :
    ↥(K0 ×ˢ J) ⊕ ↥(K1 ×ˢ J) ≃ₜ ↥((Sum.inl '' K0 ∪ Sum.inr '' K1) ×ˢ J) :=
  ((Homeomorph.sumCongr (Homeomorph.Set.prod K0 J) (Homeomorph.Set.prod K1 J)).trans
    Homeomorph.sumProdDistrib.symm).trans
      (((sumSubsetHomeomorph K0 K1).prodCongr (Homeomorph.refl J)).trans
        (Homeomorph.Set.prod (Sum.inl '' K0 ∪ Sum.inr '' K1) J).symm)

omit [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X] [TopologicalSpace T] in
theorem image_sumBicollarMap (c0 : E × T → X) (c1 : F × T → X)
    (K0 : Set E) (K1 : Set F) (J : Set T) :
    sumBicollarMap c0 c1 '' ((Sum.inl '' K0 ∪ Sum.inr '' K1) ×ˢ J) =
      c0 '' (K0 ×ˢ J) ∪ c1 '' (K1 ×ˢ J) := by
  ext x
  constructor
  · rintro ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
    rcases hz with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · exact Or.inl ⟨(a, t), ⟨ha, ht⟩, rfl⟩
    · exact Or.inr ⟨(a, t), ⟨ha, ht⟩, rfl⟩
  · rintro (⟨⟨a, t⟩, ⟨ha, ht⟩, rfl⟩ | ⟨⟨a, t⟩, ⟨ha, ht⟩, rfl⟩)
    · exact ⟨(Sum.inl a, t), ⟨Or.inl ⟨a, ha, rfl⟩, ht⟩, rfl⟩
    · exact ⟨(Sum.inr a, t), ⟨Or.inr ⟨a, ha, rfl⟩, ht⟩, rfl⟩

theorem isEmbedding_sumBicollarMap [T2Space X]
    {K0 : Set E} {K1 : Set F} {J : Set T}
    (hK0 : IsCompact K0) (hK1 : IsCompact K1) (hJ : IsCompact J)
    (c0 : E × T → X) (c1 : F × T → X)
    (hi0 : IsEmbedding (fun z : (K0 ×ˢ J : Set (E × T)) => c0 z))
    (hi1 : IsEmbedding (fun z : (K1 ×ˢ J : Set (F × T)) => c1 z))
    (hdis : Disjoint (c0 '' (K0 ×ˢ J)) (c1 '' (K1 ×ˢ J))) :
    IsEmbedding (fun z : ((Sum.inl '' K0 ∪ Sum.inr '' K1) ×ˢ J : Set ((E ⊕ F) × T)) =>
      sumBicollarMap c0 c1 z) := by
  let : CompactSpace ↥(K0 ×ˢ J) := isCompact_iff_compactSpace.mp (hK0.prod hJ)
  let : CompactSpace ↥(K1 ×ˢ J) := isCompact_iff_compactSpace.mp (hK1.prod hJ)
  have h0 : IsClosed (range (fun z : (K0 ×ˢ J : Set (E × T)) => c0 z)) :=
    (isCompact_range hi0.continuous).isClosed
  have h1 : IsClosed (range (fun z : (K1 ×ˢ J : Set (F × T)) => c1 z)) :=
    (isCompact_range hi1.continuous).isClosed
  have hd : Disjoint (range (fun z : (K0 ×ˢ J : Set (E × T)) => c0 z))
      (range (fun z : (K1 ×ˢ J : Set (F × T)) => c1 z)) := by
    exact hdis.mono (by rintro _ ⟨z, rfl⟩; exact ⟨z, z.property, rfl⟩)
      (by rintro _ ⟨z, rfl⟩; exact ⟨z, z.property, rfl⟩)
  have hs := hi0.sumElim hi1 (by simpa only [h0.closure_eq] using hd)
    (by simpa only [h1.closure_eq] using hd)
  let H := sumSubsetProdHomeomorph K0 K1 J
  convert hs.comp H.symm.isEmbedding using 1
  funext z
  obtain ⟨w, rfl⟩ := H.surjective z
  simp only [Function.comp_apply, H.symm_apply_apply]
  cases w <;> rfl

end Poincare.Topology
