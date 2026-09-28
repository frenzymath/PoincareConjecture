import PoincareConjecture.Proofs.M76.Mathlib.ConvexIntrinsicInterior
import Mathlib.Analysis.Convex.Topology










set_option autoImplicit false

open Set

namespace Convex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem combo_intrinsicInterior_self_mem {S : Set E} (hS : Convex ℝ S)
    {x y : E} (hx : x ∈ intrinsicInterior ℝ S) (hy : y ∈ S)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x + b • y ∈ intrinsicInterior ℝ S := by
  let P := affineSpan ℝ S
  let pP : P := ⟨x, subset_affineSpan ℝ S (intrinsicInterior_subset hx)⟩
  let : Nonempty P := ⟨pP⟩
  let e : P.direction ≃ᵃⁱ[ℝ] P := AffineIsometryEquiv.vaddConst ℝ pP
  let A : P.direction →ᵃⁱ[ℝ] E := P.subtypeₐᵢ.comp e.toAffineIsometry
  let B : Set P := Subtype.val ⁻¹' S
  let C : Set P.direction := A ⁻¹' S
  have hC : Convex ℝ C := hS.affine_preimage A.toAffineMap
  have himage : A '' interior C = intrinsicInterior ℝ S := by
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
  obtain ⟨x', hx', hxx⟩ := himage.symm.subset hx
  let y' := e.symm ⟨y, subset_affineSpan ℝ S hy⟩
  have hyy : A y' = y := by
    change (e (e.symm ⟨y, subset_affineSpan ℝ S hy⟩) : E) = y
    rw [e.apply_symm_apply]
  have hy' : y' ∈ C := by
    change A y' ∈ S
    rwa [hyy]
  apply himage.subset
  refine ⟨a • x' + b • y', hC.combo_interior_self_mem_interior hx' hy' ha hb hab, ?_⟩
  have ha' : a = 1 - b := by linarith
  have hcombo : a • x' + b • y' = b • (y' - x') + x' := by
    rw [ha']
    module
  rw [hcombo]
  change A.toAffineMap (b • (y' -ᵥ x') +ᵥ x') = _
  rw [AffineMap.map_vadd, map_smul, AffineMap.linearMap_vsub]
  change b • (A y' - A x') + A x' = _
  rw [hxx, hyy, ha']
  module




theorem intrinsicInterior_union_of_subset {S T : Set E}
    (hS : Convex ℝ S) (hT : Convex ℝ T) (hTS : T ⊆ S) :
    Convex ℝ (intrinsicInterior ℝ S ∪ intrinsicInterior ℝ T) := by
  intro x hx y hy a b ha hb hab
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Or.inl (hS.intrinsicInterior hx hy ha hb hab)
  · by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      rw [ha0, hb1, zero_smul, one_smul, zero_add]
      exact Or.inr hy
    · exact Or.inl (hS.combo_intrinsicInterior_self_mem hx
        (hTS (intrinsicInterior_subset hy)) (lt_of_le_of_ne ha (Ne.symm ha0)) hb hab)
  · by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith
      rw [hb0, ha1, zero_smul, one_smul, add_zero]
      exact Or.inr hx
    · have h := hS.combo_intrinsicInterior_self_mem hy
        (hTS (intrinsicInterior_subset hx)) (lt_of_le_of_ne hb (Ne.symm hb0)) ha
        (by linarith : b + a = 1)
      exact Or.inl (add_comm (b • y) (a • x) ▸ h)
  · exact Or.inr (hT.intrinsicInterior hx hy ha hb hab)

end Convex
