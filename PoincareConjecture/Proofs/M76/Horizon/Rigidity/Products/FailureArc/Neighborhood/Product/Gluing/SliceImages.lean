import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Gluing.Attached



set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.Dehn.Annuli.ProductGluing

theorem attached_slice_range
    {X C D T : Type*} (b : C → X) (c : D → X)
    (f : C × T → X) (g : D × T → X)
    (H : (range b ∪ range c : Set X) × T → X)
    (hf : ∀ x t, H (⟨b x, Or.inl (mem_range_self x)⟩, t) = f (x, t))
    (hg : ∀ y t, H (⟨c y, Or.inr (mem_range_self y)⟩, t) = g (y, t))
    (t : T) :
    range (fun x => H (x, t)) =
      range (fun x => f (x, t)) ∪ range (fun y => g (y, t)) := by
  ext z
  constructor
  · rintro ⟨⟨x, hx⟩, rfl⟩
    rcases hx with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · exact Or.inl ⟨x, (hf x t).symm⟩
    · exact Or.inr ⟨y, (hg y t).symm⟩
  · rintro (⟨x, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨⟨b x, Or.inl (mem_range_self x)⟩, hf x t⟩
    · exact ⟨⟨c y, Or.inr (mem_range_self y)⟩, hg y t⟩

end PoincareConjecture.M76.Dehn.Annuli.ProductGluing
