import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.RegularClosedAttachment

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks

theorem relative_regular_closed_of_homeomorph_open_closure
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (H : X ≃ₜ Y) {O C : Set X} (hO : IsOpen O) (hC : closure O = C) :
    closure (interior (H '' C)) = H '' C := by
  rw [← H.image_interior, ← H.image_closure, ← hC]
  apply congrArg (Set.image H)
  exact Subset.antisymm isClosed_closure.closure_interior_subset
    (closure_mono hO.subset_interior_closure)

theorem pure_of_homeomorph_open_closure
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (H : X ≃ₜ K.space) {O C : Set X}
    (hO : IsOpen O) (hC : closure O = C)
    (hN : (Subtype.val : K.space → E) ⁻¹' N.space = H '' C) :
    ∀ s ∈ N.faces, ∃ t ∈ N.faces, t.card = 3 ∧ s ⊆ t := by
  apply K.pure_of_relative_regular_closed N hK hNK hpure
  rw [hN]
  exact relative_regular_closed_of_homeomorph_open_closure H hO hC

theorem pure_of_original_open_closure
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K L N : SimplicialComplex ℝ E) (hL : L.faces.Finite) (hNL : N ≤ L)
    (hpure : ∀ s ∈ L.faces, ∃ t ∈ L.faces, t.card = 3 ∧ s ⊆ t)
    (hLK : L.space = K.space) {S O C : Set X}
    (H : K.space ≃ₜ S) (a : E → X)
    (haval : ∀ x : K.space, a x = (H x : X))
    (hO : IsOpen ((Subtype.val : S → X) ⁻¹' O))
    (hC : closure ((Subtype.val : S → X) ⁻¹' O) = Subtype.val ⁻¹' C)
    (hN : N.space = K.space ∩ a ⁻¹' C) :
    ∀ s ∈ N.faces, ∃ t ∈ N.faces, t.card = 3 ∧ s ⊆ t := by
  let G : L.space ≃ₜ S := (Homeomorph.setCongr hLK).trans H
  have hpre : (Subtype.val : L.space → E) ⁻¹' N.space =
      G ⁻¹' ((Subtype.val : S → X) ⁻¹' C) := by
    ext x
    have hxK : (x : E) ∈ K.space := hLK.subset x.property
    change (x : E) ∈ N.space ↔ (H ⟨x, hxK⟩ : X) ∈ C
    rw [hN]
    change ((x : E) ∈ K.space ∧ a x ∈ C) ↔ _
    rw [haval ⟨x, hxK⟩]
    exact and_iff_right hxK
  apply L.pure_of_relative_regular_closed N hL hNL hpure
  rw [hpre, ← G.preimage_interior, ← G.preimage_closure, ← hC]
  congr 1
  exact Subset.antisymm isClosed_closure.closure_interior_subset
    (closure_mono hO.subset_interior_closure)

end PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
