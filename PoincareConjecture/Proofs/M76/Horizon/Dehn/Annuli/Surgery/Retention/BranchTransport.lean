import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.OpenSourceCopy

set_option autoImplicit false
open Set Topology

namespace PoincareConjecture.M76.Dehn.Annuli



theorem retained_source_transport_branch
    {E Y X : Type*} [TopologicalSpace E] [TopologicalSpace Y] [TopologicalSpace X]
    {f : E → X} {g : Y → X} {S U A : Set E} {T V : Set Y}
    (hUS : U ⊆ S) (hVT : V ⊆ T)
    (hV : IsOpen ((Subtype.val : T → Y) ⁻¹' V))
    (H : U ≃ₜ V) (hkeep : ∀ x : U, g (H x) = f x)
    (hA : IsOpen ((Subtype.val : S → E) ⁻¹' A))
    (he : IsEmbedding (fun x : A ↦ f x)) :
    let B := (fun x : U ↦ (H x : Y)) '' (Subtype.val ⁻¹' A)
    B ⊆ T ∧ IsOpen ((Subtype.val : T → Y) ⁻¹' B) ∧
      IsEmbedding (fun x : B ↦ g x) ∧ g '' B = f '' (U ∩ A) := by
  let h : U → Y := fun x ↦ H x
  let W : Set U := Subtype.val ⁻¹' A
  have hW : IsOpen W := hA.preimage
    (continuous_subtype_val.subtype_mk (fun x ↦ hUS x.property))
  have hh : IsEmbedding h := IsEmbedding.subtypeVal.comp H.isEmbedding
  let F := hh.homeomorphImage W
  have hF (x : W) : (F x : Y) = h x.val := rfl
  have hinc : IsEmbedding (fun x : W ↦ (⟨x.val, x.property⟩ : A)) :=
    (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).codRestrict _ _
  have he' : IsEmbedding (fun x : W ↦ f x.val) := he.comp hinc
  have hnew : IsEmbedding (fun x : h '' W ↦ g x) := by
    have hem := he'.comp F.symm.isEmbedding
    have heq : (fun x : h '' W ↦ f (F.symm x).val) = (fun x : h '' W ↦ g x) := by
      funext x
      have hk := hkeep (F.symm x).val
      change g (h (F.symm x).val) = _ at hk
      rw [← hF, F.apply_symm_apply] at hk
      exact hk.symm
    exact heq ▸ hem
  refine ⟨?_, ?_, hnew, ?_⟩
  · rintro _ ⟨x, _, rfl⟩
    exact hVT (H x).property
  · let q : U → T := fun x ↦ ⟨H x, hVT (H x).property⟩
    have hq : IsOpenMap q :=
      (IsOpenEmbedding.inclusion hVT hV).isOpenMap.comp H.isOpenMap
    have heq : (Subtype.val : T → Y) ⁻¹' (h '' W) = q '' W := by
      ext y
      constructor
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, Subtype.ext hxy⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
    change IsOpen ((Subtype.val : T → Y) ⁻¹' (h '' W))
    rw [heq]
    exact hq _ hW
  · ext z
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, ⟨x.property, hx⟩, (hkeep x).symm⟩
    · rintro ⟨x, ⟨hxU, hxA⟩, rfl⟩
      exact ⟨H ⟨x, hxU⟩, ⟨⟨x, hxU⟩, hxA, rfl⟩, hkeep ⟨x, hxU⟩⟩


theorem isCompact_source_sdiff_of_relative_open
    {E : Type*} [TopologicalSpace E] {S U : Set E} (hS : IsCompact S)
    (hU : IsOpen ((Subtype.val : S → E) ⁻¹' U)) : IsCompact (S \ U) := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have heq : (Subtype.val : S → E) '' ((Subtype.val : S → E) ⁻¹' U)ᶜ = S \ U := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hx, hn⟩
      exact ⟨⟨x, hx⟩, hn, rfl⟩
  rw [← heq]
  exact hU.isClosed_compl.isCompact.image continuous_subtype_val

end PoincareConjecture.M76.Dehn.Annuli
