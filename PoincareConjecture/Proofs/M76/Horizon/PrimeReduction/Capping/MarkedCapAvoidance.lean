import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Lattice








set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

theorem disjoint_model_image_caps
    {X Y κ : Type*} {Q A : Set X} {K : Set Y}
    (f : X → Y) (B : κ → Set X) (caps : κ → Set Y)
    (hfi : InjOn f Q) (hK : K = f '' Q) (hBQ : ∀ b, B b ⊆ Q)
    (hattach : ∀ b, caps b ∩ K = f '' B b)
    (hAQ : A ⊆ Q) (hAB : Disjoint A (⋃ b, B b)) :
    Disjoint (f '' A) (⋃ b, caps b) := by
  apply disjoint_left.mpr
  rintro y ⟨x, hx, rfl⟩ hy
  obtain ⟨b, hb⟩ := mem_iUnion.mp hy
  have hxK : f x ∈ K := hK.symm ▸ mem_image_of_mem f (hAQ hx)
  obtain ⟨z, hz, hzx⟩ := (hattach b).subset ⟨hb, hxK⟩
  have hzx' : z = x := hfi (hBQ b hz) (hAQ hx) hzx
  exact disjoint_left.mp hAB hx (mem_iUnion.mpr ⟨b, hzx' ▸ hz⟩)

end PoincareConjecture.M76
