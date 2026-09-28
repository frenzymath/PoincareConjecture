import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicFaceSaturation

set_option autoImplicit false

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem Convex.subset_closure_intrinsicInterior {s : Set E} (hs : Convex ℝ s) :
    s ⊆ closure (intrinsicInterior ℝ s) := by
  intro x hx
  let A := affineSpan ℝ s
  let p : A := ⟨x, subset_affineSpan ℝ s hx⟩
  let : Nonempty A := ⟨p⟩
  let e := (AffineIsometryEquiv.constVSub ℝ p).symm.toHomeomorph
  let C := e ⁻¹' ((Subtype.val : A → E) ⁻¹' s)
  let f : A.direction → E := fun v => (e v : E)
  have hcv : Convex ℝ C := hs.affine_preimage
    (A.subtype.comp (AffineIsometryEquiv.constVSub ℝ p).symm.toAffineEquiv.toAffineMap)
  have hI : f '' interior C = intrinsicInterior ℝ s := by
    change (Subtype.val ∘ e) '' interior C = _
    rw [image_comp, e.image_interior, Homeomorph.image_preimage]
    rfl
  have hne : (interior C).Nonempty := by
    rw [← image_nonempty (f := f), hI]
    exact Set.Nonempty.intrinsicInterior hs ⟨x, hx⟩
  have hpC : e.symm p ∈ C := by
    change (e (e.symm p) : E) ∈ s
    simpa only [e.apply_symm_apply] using hx
  have hcl : e.symm p ∈ closure (interior C) := by
    rw [hcv.closure_interior_eq_closure_of_nonempty_interior hne]
    exact subset_closure hpC
  rw [← hI]
  apply image_closure_subset_closure_image
    (continuous_subtype_val.comp e.continuous)
  exact ⟨e.symm p, hcl, congrArg Subtype.val (e.apply_symm_apply p)⟩

theorem Convex.intrinsicInterior_inter_open_nonempty {s U : Set E}
    (hs : Convex ℝ s) (hU : IsOpen U) (hne : (s ∩ U).Nonempty) :
    (intrinsicInterior ℝ s ∩ U).Nonempty := by
  obtain ⟨x, hxs, hxU⟩ := hne
  obtain ⟨y, hyU, hys⟩ := mem_closure_iff.mp
    (hs.subset_closure_intrinsicInterior hxs) U hU hxU
  exact ⟨y, hys, hyU⟩
