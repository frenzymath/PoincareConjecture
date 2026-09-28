import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Intervals.Source.SourceModel



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)

theorem copied_pair_selected_fibers
    {X : Type*} {S T C D : Set P2} {f₀ f₁ f : P2 → X}
    (a : P2 ≃ᴬ[ℝ] P2) (hC : C ⊆ S) (hD : D ⊆ T)
    (hfi : InjOn f₀ S) (hgi : InjOn f₁ T)
    (hkeep₀ : EqOn f f₀ S) (hkeep₁ : ∀ x ∈ T, f (a x) = f₁ x)
    (himage : f₀ '' C = f₁ '' D) :
    ∀ x ∈ S ∪ a '' T, f x ∈ f '' C ↔ x ∈ C ∪ a '' D := by
  have hfirst : f '' C = f₀ '' C := image_congr (hkeep₀.mono hC)
  intro x hx
  rw [hfirst]
  constructor
  · intro hxc
    rcases hx with hx | ⟨y,hy,rfl⟩
    · obtain ⟨y,hy,hyx⟩ := hxc
      have hyx' : y = x := hfi (hC hy) hx (hyx.trans (hkeep₀ hx))
      exact Or.inl (hyx' ▸ hy)
    · have hyim : f₁ y ∈ f₁ '' D := himage.subset ((hkeep₁ y hy) ▸ hxc)
      obtain ⟨z,hz,hzy⟩ := hyim
      exact Or.inr ⟨z,hz,congrArg a (hgi (hD hz) hy hzy)⟩
  · rintro (hxC | ⟨y,hy,rfl⟩)
    · exact ⟨x,hxC,(hkeep₀ (hC hxC)).symm⟩
    · rw [hkeep₁ y (hD hy)]
      exact himage.symm.subset ⟨y,hy,rfl⟩

theorem copied_pair_selected_complement_closed
    {X : Type*} {S T A B C : Set P2} {f : P2 → X}
    (a : P2 ≃ᴬ[ℝ] P2) (hdis : Disjoint S (a '' T))
    (hC : C ⊆ S) (hB : B ⊆ T)
    (hdouble : doubleLocusOn f (S ∪ a '' T) = A ∪ a '' B)
    (hrest : IsClosed (A \ C)) (hclosedB : IsClosed B) :
    IsClosed (doubleLocusOn f (S ∪ a '' T) \ C) := by
  have hd : Disjoint (a '' B) C := (hdis.mono hC (image_mono hB)).symm
  rw [hdouble,union_sdiff_distrib,hd.sdiff_eq_left]
  exact hrest.union (a.toHomeomorph.isClosedMap _ hclosedB)

end PoincareConjecture.M76.Dehn.Annuli
