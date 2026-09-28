import PoincareConjecture.Proofs.M76.Wall.Mathlib.RelativeFilledFrontier
import Mathlib.Topology.Homeomorph.Lemmas










set_option autoImplicit false
open Set

namespace Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {R D : Set X} {Q : Set Y}



theorem mem_interior_image_subdomain_iff (C : R ≃ₜ Q)
    (hmark : ∀ x : R, (x : X) ∈ frontier R ↔ (C x : Y) ∈ frontier Q)
    (hDR : D ⊆ R) (x : R) :
    (C x : Y) ∈ interior ((Subtype.val : Q → Y) ''
      (C '' ((Subtype.val : R → X) ⁻¹' D))) ↔ (x : X) ∈ interior D := by
  let T : Set Q := C '' ((Subtype.val : R → X) ⁻¹' D)
  let E : Set Y := (Subtype.val : Q → Y) '' T
  have hEQ : E ⊆ Q := by rintro _ ⟨y, _, rfl⟩; exact y.property
  have hpre : (Subtype.val : Q → Y) ⁻¹' E = T := by
    ext y
    simp only [E, mem_preimage, mem_image, Subtype.val_inj, exists_eq_right]
  have hparent : (C x : Y) ∈ interior Q ↔ (x : X) ∈ interior R := by
    rw [mem_interior_iff_notMem_frontier (C x).property,
      mem_interior_iff_notMem_frontier x.property]
    exact not_congr (hmark x).symm
  have hrel : C x ∈ interior ((Subtype.val : Q → Y) ⁻¹' E) ↔
      x ∈ interior ((Subtype.val : R → X) ⁻¹' D) := by
    rw [hpre, show T = C '' ((Subtype.val : R → X) ⁻¹' D) from rfl,
      ← C.image_interior]
    exact C.injective.mem_set_image
  change (C x : Y) ∈ interior E ↔ (x : X) ∈ interior D
  constructor
  · intro hx
    have hxQ := interior_mono hEQ hx
    exact (mem_interior_subtype_preimage_iff_of_mem_interior x (hparent.mp hxQ)).mp
      (hrel.mp (preimage_interior_subset_interior_preimage continuous_subtype_val hx))
  · intro hx
    have hxR := interior_mono hDR hx
    exact (mem_interior_subtype_preimage_iff_of_mem_interior (C x) (hparent.mpr hxR)).mp
      (hrel.mpr (preimage_interior_subset_interior_preimage continuous_subtype_val hx))



theorem interior_image_subdomain (C : R ≃ₜ Q)
    (hmark : ∀ x : R, (x : X) ∈ frontier R ↔ (C x : Y) ∈ frontier Q)
    (hDR : D ⊆ R) :
    interior ((Subtype.val : Q → Y) '' (C '' ((Subtype.val : R → X) ⁻¹' D))) =
      (Subtype.val : Q → Y) '' (C '' ((Subtype.val : R → X) ⁻¹' interior D)) := by
  ext y
  constructor
  · intro hy
    obtain ⟨_, ⟨x, _, rfl⟩, rfl⟩ := interior_subset hy
    exact ⟨C x, ⟨x, (C.mem_interior_image_subdomain_iff hmark hDR x).mp hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact (C.mem_interior_image_subdomain_iff hmark hDR x).mpr hx



theorem closure_image_subdomain (C : R ≃ₜ Q) (hQ : IsClosed Q)
    (hDR : closure D ⊆ R) :
    closure ((Subtype.val : Q → Y) '' (C '' ((Subtype.val : R → X) ⁻¹' D))) =
      (Subtype.val : Q → Y) '' (C '' ((Subtype.val : R → X) ⁻¹' closure D)) := by
  rw [hQ.isClosedMap_subtype_val.closure_image_eq_of_continuous continuous_subtype_val,
    ← C.image_closure, Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
    image_preimage_eq_of_subset (by simpa using subset_closure.trans hDR)]



theorem frontier_image_subdomain (C : R ≃ₜ Q) (hQ : IsClosed Q) (hD : IsClosed D)
    (hmark : ∀ x : R, (x : X) ∈ frontier R ↔ (C x : Y) ∈ frontier Q)
    (hDR : D ⊆ R) :
    frontier ((Subtype.val : Q → Y) '' (C '' ((Subtype.val : R → X) ⁻¹' D))) =
      (Subtype.val : Q → Y) '' (C '' ((Subtype.val : R → X) ⁻¹' frontier D)) := by
  have hclosed : IsClosed ((Subtype.val : Q → Y) ''
      (C '' ((Subtype.val : R → X) ⁻¹' D))) :=
    hQ.isClosedMap_subtype_val _ (C.isClosedMap _ (hD.preimage continuous_subtype_val))
  rw [hclosed.frontier_eq, hD.frontier_eq]
  ext y
  constructor
  · rintro ⟨⟨_, ⟨x, hxD, rfl⟩, rfl⟩, hxI⟩
    exact ⟨C x, ⟨x, ⟨hxD, fun hx => hxI
      ((C.mem_interior_image_subdomain_iff hmark hDR x).mpr hx)⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, ⟨hxD, hxI⟩, rfl⟩, rfl⟩
    exact ⟨⟨C x, ⟨x, hxD, rfl⟩, rfl⟩,
      fun hx => hxI ((C.mem_interior_image_subdomain_iff hmark hDR x).mp hx)⟩

end Homeomorph
