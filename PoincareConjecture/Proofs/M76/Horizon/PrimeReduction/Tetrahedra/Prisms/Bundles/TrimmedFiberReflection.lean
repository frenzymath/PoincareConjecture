import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.SymmetricPrismTrim



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

theorem trimProduct_reflection {E : Type*} [TopologicalSpace E] (A : Set E)
    (x : (A ×ˢ I : Set (E × ℝ))) :
    trimProduct A (productFiberReflection A x) = productFiberReflection A (trimProduct A x) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change 1/4+(1-(x : E × ℝ).2)/2 = 1-(1/4+(x : E × ℝ).2/2)
    ring

theorem prismFiberReflection_trim_chart
    {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B)
    (C : (A ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrim H)
    (hC : ∀ x, (C x : E) = H (trimProduct A x)) (x : prismTrim H) :
    (prismFiberReflection C x : E) =
      prismFiberReflection H ⟨x,prismTrim_subset H x.property⟩ := by
  let y := C.symm x
  have hx : (x : E) = H (trimProduct A y) := by
    simpa only [y,C.apply_symm_apply] using hC y
  have hsource : H.symm ⟨x,prismTrim_subset H x.property⟩ = trimProduct A y := by
    apply H.injective
    exact (H.apply_symm_apply _).trans (Subtype.ext hx)
  change (C (productFiberReflection A y) : E) =
    H (productFiberReflection A (H.symm ⟨x,prismTrim_subset H x.property⟩))
  rw [hC,trimProduct_reflection,hsource]

theorem prismTrim_reflection_invariant
    {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (x : B) :
    (prismFiberReflection H x : E) ∈ prismTrim H ↔ (x : E) ∈ prismTrim H := by
  rw [mem_prismTrim_iff,mem_prismTrim_iff]
  change (H.symm (H (productFiberReflection A (H.symm x))) : E × ℝ).2 ∈ _ ↔ _
  rw [H.symm_apply_apply,productFiberReflection_value]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

end PoincareConjecture.M76.PrismBelt
