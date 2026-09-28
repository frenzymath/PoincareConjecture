import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Separation.Hausdorff










set_option autoImplicit false

open Set
open scoped Topology

universe u

namespace PoincareConjecture.Proofs.M83

variable {X : Type u} [TopologicalSpace X]



theorem involutionQuotient_isOpenMap
    (s : Setoid X) (a : X ≃ₜ X) (ha : Function.Involutive a)
    (hs : ∀ x y : X, s.r x y ↔ x = y ∨ x = a y) :
    IsOpenMap (Quotient.mk s) := by
  intro U hU
  have he : (Quotient.mk s) ⁻¹' ((Quotient.mk s) '' U) = U ∪ a '' U := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      rcases (hs x y).mp (Quotient.exact hxy.symm) with h | h
      · exact Or.inl (h ▸ hy)
      · exact Or.inr ⟨y, hy, h.symm⟩
    · rintro (hx | ⟨y, hy, rfl⟩)
      · exact ⟨x, hx, rfl⟩
      · exact ⟨y, hy, Quotient.sound ((hs y (a y)).mpr (Or.inr (ha y).symm))⟩
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  change IsOpen ((Quotient.mk s) ⁻¹' ((Quotient.mk s) '' U))
  rw [he]
  exact hU.union (a.isOpenMap U hU)



theorem involutionQuotient_isLocalHomeomorph [T2Space X]
    (s : Setoid X) (a : X ≃ₜ X) (ha : Function.Involutive a)
    (hfree : ∀ x : X, x ≠ a x)
    (hs : ∀ x y : X, s.r x y ↔ x = y ∨ x = a y) :
    IsLocalHomeomorph (Quotient.mk s) := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro x
  obtain ⟨U, V, hU, hV, hxU, haxV, hUV⟩ := t2_separation (hfree x)
  let W : Set X := U ∩ a ⁻¹' V
  have hW : IsOpen W := hU.inter (hV.preimage a.continuous)
  have hxW : x ∈ W := ⟨hxU, haxV⟩
  refine ⟨W, hW.mem_nhds hxW, ?_⟩
  apply _root_.Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_quotient_mk'.comp continuous_subtype_val
  · intro y z hyz
    rcases (hs y z).mp (Quotient.exact hyz) with h | h
    · exact Subtype.ext h
    · exact False.elim (Set.disjoint_left.mp hUV y.property.1 (h ▸ z.property.2))
  · exact (involutionQuotient_isOpenMap s a ha hs).comp hW.isOpenMap_subtype_val

end PoincareConjecture.Proofs.M83
