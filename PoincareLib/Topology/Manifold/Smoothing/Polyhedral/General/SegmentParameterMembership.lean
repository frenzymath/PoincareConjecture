import Mathlib.Analysis.Convex.Segment
import Mathlib.Data.Real.Basic

/-!
# Exact segment membership under affine parameter matching

An injective map matching affine parameters on a whole segment
identifies both the closed and the open segment. This controls
the diagonal and its endpoints in Erickson's polygon disk gluing,
pp. 8--10. See M76 derivation 118.
-/

set_option autoImplicit false

open Set

namespace Function.Injective

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {s : Set E} {f : s → F} {a b : E} {c d : F}

/-- Matching all affine parameters under an injective map
gives exact membership in the two closed segments.
See M76 derivation 118. -/
theorem segment_mem_iff_of_lineMap (hf : Function.Injective f) (hs : segment ℝ a b ⊆ s)
    (hparam : ∀ (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1)
      (hx : AffineMap.lineMap a b t ∈ s), f ⟨AffineMap.lineMap a b t, hx⟩ = AffineMap.lineMap c d t)
    (x : s) : (x : E) ∈ segment ℝ a b ↔ f x ∈ segment ℝ c d := by
  rw [segment_eq_image_lineMap, segment_eq_image_lineMap]
  constructor
  · rintro ⟨t, ht, htx⟩
    have hx := hs (lineMap_mem_segment ℝ a b ht)
    have he := hparam t ht hx
    have hsub : (⟨AffineMap.lineMap a b t, hx⟩ : s) = x := Subtype.ext htx
    rw [hsub] at he
    exact ⟨t, ht, he.symm⟩
  · rintro ⟨t, ht, htx⟩
    have hx := hs (lineMap_mem_segment ℝ a b ht)
    have he := hf ((hparam t ht hx).trans htx)
    exact ⟨t, ht, congrArg (fun z : s => (z : E)) he⟩

/-- The same affine parameter matching identifies the open
segments exactly, retaining the distinction at their endpoints.
This also handles degenerate segments. See derivation 118. -/
theorem openSegment_mem_iff_of_lineMap (hf : Function.Injective f) (hs : segment ℝ a b ⊆ s)
    (hparam : ∀ (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1)
      (hx : AffineMap.lineMap a b t ∈ s), f ⟨AffineMap.lineMap a b t, hx⟩ = AffineMap.lineMap c d t)
    (x : s) : (x : E) ∈ openSegment ℝ a b ↔ f x ∈ openSegment ℝ c d := by
  rw [openSegment_eq_image_lineMap, openSegment_eq_image_lineMap]
  constructor
  · rintro ⟨t, ht, htx⟩
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have hx := hs (lineMap_mem_segment ℝ a b ht')
    have he := hparam t ht' hx
    have hsub : (⟨AffineMap.lineMap a b t, hx⟩ : s) = x := Subtype.ext htx
    rw [hsub] at he
    exact ⟨t, ht, he.symm⟩
  · rintro ⟨t, ht, htx⟩
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have hx := hs (lineMap_mem_segment ℝ a b ht')
    have he := hf ((hparam t ht' hx).trans htx)
    exact ⟨t, ht, congrArg (fun z : s => (z : E)) he⟩

end Function.Injective
