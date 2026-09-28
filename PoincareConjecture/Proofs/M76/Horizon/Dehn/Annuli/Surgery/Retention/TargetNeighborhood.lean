import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.BranchTransport

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.Dehn.Annuli

theorem exists_retained_target_neighborhood
    {E Y X : Type*} [TopologicalSpace E] [TopologicalSpace Y]
    [TopologicalSpace X] [T2Space X]
    {f : E → X} {g : Y → X} {S U : Set E} {T V : Set Y}
    (hS : IsCompact S) (hT : IsCompact T) (hUS : U ⊆ S) (hVT : V ⊆ T)
    (hU : IsOpen ((Subtype.val : S → E) ⁻¹' U))
    (hV : IsOpen ((Subtype.val : T → Y) ⁻¹' V))
    (hf : ContinuousOn f S) (hg : ContinuousOn g T)
    (H : U ≃ₜ V) (hkeep : ∀ x : U, g (H x) = f x)
    {z : X} (hfold : ∀ x ∈ S, f x = z → x ∈ U)
    (hfnew : ∀ x ∈ T, g x = z → x ∈ V)
    (W0 : Set X) (hW0 : IsOpen W0) (hzW0 : z ∈ W0) :
    ∃ W : Set X, IsOpen W ∧ z ∈ W ∧ W ⊆ W0 ∧
      (∀ x ∈ S, f x ∈ W → x ∈ U) ∧
      (∀ x ∈ T, g x ∈ W → x ∈ V) ∧ g '' T ∩ W = f '' S ∩ W := by
  have hclosedF : IsClosed (f '' (S \ U)) :=
    ((isCompact_source_sdiff_of_relative_open hS hU).image_of_continuousOn
      (hf.mono sdiff_subset)).isClosed
  have hclosedG : IsClosed (g '' (T \ V)) :=
    ((isCompact_source_sdiff_of_relative_open hT hV).image_of_continuousOn
      (hg.mono sdiff_subset)).isClosed
  let W := W0 ∩ (f '' (S \ U) ∪ g '' (T \ V))ᶜ
  have hcutF (x : E) (hx : x ∈ S) (hxW : f x ∈ W) : x ∈ U := by
    by_contra hn
    exact hxW.2 (Or.inl ⟨x, ⟨hx, hn⟩, rfl⟩)
  have hcutG (x : Y) (hx : x ∈ T) (hxW : g x ∈ W) : x ∈ V := by
    by_contra hn
    exact hxW.2 (Or.inr ⟨x, ⟨hx, hn⟩, rfl⟩)
  refine ⟨W, hW0.inter (hclosedF.union hclosedG).isOpen_compl,
    ⟨hzW0, ?_⟩, inter_subset_left, hcutF, hcutG, ?_⟩
  · rintro (⟨x, ⟨hx, hn⟩, hxz⟩ | ⟨x, ⟨hx, hn⟩, hxz⟩)
    · exact hn (hfold x hx hxz)
    · exact hn (hfnew x hx hxz)
  · ext w
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hw⟩
      let a := H.symm ⟨x, hcutG x hx hw⟩
      have ha : f a = g x := by
        rw [← hkeep a]
        exact congrArg (fun y : V ↦ g y) (H.apply_symm_apply ⟨x, hcutG x hx hw⟩)
      exact ⟨⟨a, hUS a.property, ha⟩, hw⟩
    · rintro ⟨⟨x, hx, rfl⟩, hw⟩
      let a : U := ⟨x, hcutF x hx hw⟩
      exact ⟨⟨H a, hVT (H a).property, hkeep a⟩, hw⟩

theorem source_double_fiber_subset
    {E X : Type*} {f : E → X} {S U : Set E}
    (p : doubleLocusOn f S → doubleLocusOn f S)
    (hunique : ∀ (x : doubleLocusOn f S) (y : E), y ∈ S →
      f x = f y → (x : E) ≠ y → y = (p x : E))
    {a b : E} (ha : a ∈ S) (hb : b ∈ S) (hab : f a = f b) (hne : a ≠ b)
    (haU : a ∈ U) (hbU : b ∈ U) : S ∩ f ⁻¹' {f a} ⊆ U := by
  let aG : doubleLocusOn f S := ⟨a, ha, b, hb, hab, hne⟩
  intro z hz
  by_cases hza : z = a
  · exact hza ▸ haU
  · have hzb : z = b := (hunique aG z hz.1 hz.2.symm (Ne.symm hza)).trans
      (hunique aG b hb hab hne).symm
    exact hzb ▸ hbU

end PoincareConjecture.M76.Dehn.Annuli
