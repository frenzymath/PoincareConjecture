import Mathlib.Analysis.Convex.Intrinsic










set_option autoImplicit false

open Set




protected theorem Convex.intrinsicInterior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : Convex ℝ S) : Convex ℝ (intrinsicInterior ℝ S) := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · rw [intrinsicInterior_empty]
    exact convex_empty
  let P := affineSpan ℝ S
  let pP : P := ⟨p, subset_affineSpan ℝ S hp⟩
  let : Nonempty P := ⟨pP⟩
  let e : P.direction ≃ᵃⁱ[ℝ] P := AffineIsometryEquiv.vaddConst ℝ pP
  let a : P.direction →ᵃⁱ[ℝ] E := P.subtypeₐᵢ.comp e.toAffineIsometry
  let B : Set P := Subtype.val ⁻¹' S
  let C : Set P.direction := a ⁻¹' S
  have hC : Convex ℝ C := hS.affine_preimage a.toAffineMap
  have himage : a '' interior C = intrinsicInterior ℝ S := by
    change (Subtype.val ∘ e.toHomeomorph) '' interior (e.toHomeomorph ⁻¹' B) =
      Subtype.val '' interior B
    rw [← e.toHomeomorph.preimage_interior]
    calc
      (Subtype.val ∘ e.toHomeomorph) '' (e.toHomeomorph ⁻¹' interior B) =
          Subtype.val '' (e.toHomeomorph '' (e.toHomeomorph ⁻¹' interior B)) := by
        rw [image_image]
        rfl
      _ = Subtype.val '' interior B := by
        rw [e.toHomeomorph.surjective.image_preimage]
  rw [← himage]
  exact hC.interior.affine_image a.toAffineMap
