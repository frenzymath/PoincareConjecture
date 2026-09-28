import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.PairFibers



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)

theorem copied_pair_double_locus
    {X : Type*} {S T C D : Set P2} {f g h : P2 → X}
    (a : P2 ≃ᴬ[ℝ] P2) (hdis : Disjoint S (a '' T))
    (hfi : InjOn f S) (hgi : InjOn g T)
    (hkeep₀ : EqOn h f S) (hkeep₁ : ∀ x ∈ T, h (a x) = g x)
    (hC : {x | x ∈ S ∧ f x ∈ g '' T} = C)
    (hD : {y | y ∈ T ∧ g y ∈ f '' S} = D) :
    InjOn h S ∧ InjOn h (a '' T) ∧ doubleLocusOn h (S ∪ a '' T) = C ∪ a '' D := by
  have hi₀ : InjOn h S := by
    intro x hx y hy hxy
    exact hfi hx hy ((hkeep₀ hx).symm.trans (hxy.trans (hkeep₀ hy)))
  have hi₁ : InjOn h (a '' T) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ hxy
    exact congrArg a (hgi hx hy ((hkeep₁ x hx).symm.trans (hxy.trans (hkeep₁ y hy))))
  have himage₀ : h '' S = f '' S := image_congr hkeep₀
  have himage₁ : h '' (a '' T) = g '' T := by
    rw [← image_comp]
    exact image_congr hkeep₁
  refine ⟨hi₀,hi₁,?_⟩
  rw [double_locus_disjoint_source_pair hdis hi₀ hi₁,himage₀,himage₁]
  have hleft : {x | x ∈ S ∧ h x ∈ g '' T} = C := by
    rw [← hC]
    ext x
    exact and_congr_right (fun hx => by rw [hkeep₀ hx])
  have hright : {y | y ∈ a '' T ∧ h y ∈ f '' S} = a '' D := by
    rw [← hD]
    ext y
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,hy⟩
      exact ⟨x,⟨hx,(hkeep₁ x hx) ▸ hy⟩,rfl⟩
    · rintro ⟨x,⟨hx,hy⟩,rfl⟩
      exact ⟨⟨x,hx,rfl⟩,(hkeep₁ x hx).symm ▸ hy⟩
  rw [hleft,hright]

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
