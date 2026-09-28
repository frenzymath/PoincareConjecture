import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.Rims.RetainedReparametrization

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

theorem double_marked_component_counts_source_homeomorph
    {E Y X : Type*} [TopologicalSpace E] [TopologicalSpace Y]
    {S Q : Set E} {T P : Set Y} (H : S ≃ₜ T) {f : E → X} {g : Y → X}
    (hvalue : ∀ x : S, f x = g (H x))
    (hmark : ∀ x : S, (H x : Y) ∈ P ↔ (x : E) ∈ Q) :
    doubleBoundaryComponentCount f S Q = doubleBoundaryComponentCount g T P ∧
      doubleInteriorComponentCount f S Q = doubleInteriorComponentCount g T P := by
  let D := doubleLocusOnSourceHomeomorph H hvalue
  let C := D.isQuotientMap.isCoinducing.connectedComponentsHomeomorph fun y ↦ by
    have hfiber : D ⁻¹' {y} = {D.symm y} := by
      ext x
      exact D.toEquiv.eq_symm_apply.symm
    rw [hfiber]
    exact isConnected_singleton
  have hC (x : doubleLocusOn f S) :
      C (ConnectedComponents.mk x) = ConnectedComponents.mk (D x) := rfl
  have hDmark : D '' ((Subtype.val : doubleLocusOn f S → E) ⁻¹' Q) =
      (Subtype.val : doubleLocusOn g T → Y) ⁻¹' P := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmark ⟨x, x.property.1⟩).mpr hx
    · intro hy
      refine ⟨D.symm y, ?_, D.apply_symm_apply y⟩
      apply (hmark ⟨D.symm y, (D.symm y).property.1⟩).mp
      change (D (D.symm y) : Y) ∈ P
      rwa [D.apply_symm_apply]
  let A := ConnectedComponents.mk '' ((Subtype.val : doubleLocusOn f S → E) ⁻¹' Q)
  let B := ConnectedComponents.mk '' ((Subtype.val : doubleLocusOn g T → Y) ⁻¹' P)
  have hAB : C '' A = B := by
    change C '' (ConnectedComponents.mk '' _) = ConnectedComponents.mk '' _
    rw [image_image]
    simp only [hC]
    rw [← image_image, hDmark]
  have hcAB : C '' Aᶜ = Bᶜ := by
    rw [← hAB]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ ⟨x', hx', heq⟩
      exact hx (C.injective heq ▸ hx')
    · intro hy
      refine ⟨C.symm y, ?_, C.apply_symm_apply y⟩
      intro hx
      exact hy ⟨C.symm y, hx, C.apply_symm_apply y⟩
  change A.ncard = B.ncard ∧ Aᶜ.ncard = Bᶜ.ncard
  exact ⟨by rw [← hAB, C.injective.injOn.ncard_image],
    by rw [← hcAB, C.injective.injOn.ncard_image]⟩

end PoincareConjecture.M76.Dehn.Annuli
