import PoincareConjecture.Proofs.M76.Mathlib.OriginalCyclicProductCollar










set_option autoImplicit false

open Set CoordinateHalfBoxes

namespace Homeomorph

variable {E ι : Type*} [TopologicalSpace E]





theorem original_box_product_coordinates
    (F : ι → ((ℝ × ℝ) × ℝ) → E) {B S : Set E} {r : ℝ}
    (e : (B ×ˢ base r : Set (E × (ℝ × ℝ))) ≃ₜ (⋃ i, F i '' box r))
    (hinverse : ∀ (i : ι) (x : box r),
      (e.symm ⟨F i x, mem_iUnion.mpr ⟨i, mem_image_of_mem (F i) x.property⟩⟩ :
        E × (ℝ × ℝ)) =
          (F i ((0, (x : (ℝ × ℝ) × ℝ).1.2), 0),
            ((x : (ℝ × ℝ) × ℝ).1.1, (x : (ℝ × ℝ) × ℝ).2)))
    (A : E → ℝ) (c : ℝ)
    (hheight : ∀ i x, x ∈ box r → A (F i x) = c + x.1.1)
    (hsurface : ∀ i x, x ∈ box r → (F i x ∈ S ↔ x.2 = 0)) :
    (∀ p, A (e p) = c + (p : E × (ℝ × ℝ)).2.1) ∧
    (∀ p, (e p : E) ∈ S ↔ (p : E × (ℝ × ℝ)).2.2 = 0) ∧
    ∀ p : (B ×ˢ base r : Set (E × (ℝ × ℝ))),
      (p : E × (ℝ × ℝ)).2 = 0 → (e p : E) = (p : E × (ℝ × ℝ)).1 := by
  have hrepresentation (p : (B ×ˢ base r : Set (E × (ℝ × ℝ)))) :
      ∃ (i : ι) (x : box r), (e p : E) = F i x ∧
        (p : E × (ℝ × ℝ)) =
          (F i ((0, (x : (ℝ × ℝ) × ℝ).1.2), 0),
            ((x : (ℝ × ℝ) × ℝ).1.1, (x : (ℝ × ℝ) × ℝ).2)) := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp (e p).property
    obtain ⟨x, hx, hxe⟩ := hi
    have hpoint :
        (⟨F i x, mem_iUnion.mpr ⟨i, mem_image_of_mem (F i) hx⟩⟩ : ⋃ j, F j '' box r) =
          e p := Subtype.ext hxe
    have h := hinverse i ⟨x, hx⟩
    rw [hpoint, e.symm_apply_apply] at h
    exact ⟨i, ⟨x, hx⟩, hxe.symm, h⟩
  refine ⟨?_, ?_, ?_⟩
  · intro p
    obtain ⟨i, x, hvalue, hcoords⟩ := hrepresentation p
    have hu : (p : E × (ℝ × ℝ)).2.1 = (x : (ℝ × ℝ) × ℝ).1.1 :=
      congrArg (fun q : E × (ℝ × ℝ) => q.2.1) hcoords
    rw [hvalue, hheight i x x.property, hu]
  · intro p
    obtain ⟨i, x, hvalue, hcoords⟩ := hrepresentation p
    have hz : (p : E × (ℝ × ℝ)).2.2 = (x : (ℝ × ℝ) × ℝ).2 :=
      congrArg (fun q : E × (ℝ × ℝ) => q.2.2) hcoords
    rw [hvalue, hsurface i x x.property, hz]
  · intro p hzero
    obtain ⟨i, x, hvalue, hcoords⟩ := hrepresentation p
    have hu : (x : (ℝ × ℝ) × ℝ).1.1 = 0 :=
      (congrArg (fun q : E × (ℝ × ℝ) => q.2.1) hcoords).symm.trans
        (congrArg Prod.fst hzero)
    have hz : (x : (ℝ × ℝ) × ℝ).2 = 0 :=
      (congrArg (fun q : E × (ℝ × ℝ) => q.2.2) hcoords).symm.trans
        (congrArg Prod.snd hzero)
    have hcore : (p : E × (ℝ × ℝ)).1 = F i ((0, (x : (ℝ × ℝ) × ℝ).1.2), 0) :=
      congrArg Prod.fst hcoords
    rw [hvalue, hcore]
    exact congrArg (F i) (Prod.ext (Prod.ext hu rfl) hz)

end Homeomorph
