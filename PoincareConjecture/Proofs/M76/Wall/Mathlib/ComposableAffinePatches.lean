import PoincareConjecture.Proofs.M76.Wall.Mathlib.PLTransitionSignComparison











set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem exists_full_interior_patch (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {O : Set E} (hO : IsOpen O) (hne : O.Nonempty)
    (hOK : O ⊆ K.space) :
    ∃ t : K.FullFaceIn O, (O ∩ interior (convexHull ℝ (t.val : Set E))).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  have hxK : x ∈ interior K.space :=
    interior_mono hOK (by simpa only [hO.interior_eq] using hx)
  obtain ⟨t, ht, htc, hxt⟩ := K.exists_full_face_of_mem_interior hK hxK
  obtain ⟨y, hy, hyO⟩ :=
    (convex_convexHull ℝ (t : Set E)).intrinsicInterior_inter_open_nonempty
      hO ⟨x, hxt, hx⟩
  let b := (K.indep ht).affineBasisOfCard htc
  have hyint : y ∈ interior (convexHull ℝ (t : Set E)) := by
    have h : y ∈ interior (convexHull ℝ (range b)) :=
      b.mem_interior_convexHull_of_mem_intrinsicInterior (by simpa [b] using hy)
    simpa [b] using h
  exact ⟨⟨t, ht, htc, x, hxt, hx⟩, y, hyO, hyint⟩





theorem exists_composable_affine_patches
    (h k : OpenPartialHomeomorph E E) (K L M : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hL : L.faces.Finite) (hM : M.faces.Finite)
    (hf : K.AffineOnFaces h) (hg : L.AffineOnFaces k)
    (hcomp : M.AffineOnFaces (h.trans k))
    {U V : Set E} (hU : IsOpen U) (hne : U.Nonempty)
    (hUK : U ⊆ K.space) (hUM : U ⊆ M.space) (hUs : U ⊆ h.source)
    (hUV : MapsTo h U V) (hVL : V ⊆ L.space) (hVs : V ⊆ k.source) :
    ∃ (t : K.FullFaceIn U) (u : L.FullFaceIn V) (v : M.FullFaceIn U)
      (A B C : E →ᴬ[ℝ] E) (W : Set E),
      EqOn h A (convexHull ℝ (t.val : Set E)) ∧
      EqOn k B (convexHull ℝ (u.val : Set E)) ∧
      EqOn (h.trans k) C (convexHull ℝ (v.val : Set E)) ∧
      IsOpen W ∧ W.Nonempty ∧ W ⊆ U ∧ W ⊆ (h.trans k).source ∧
      W ⊆ interior (convexHull ℝ (t.val : Set E)) ∧
      MapsTo h W (interior (convexHull ℝ (u.val : Set E))) ∧
      W ⊆ interior (convexHull ℝ (v.val : Set E)) ∧ C = B.comp A := by
  obtain ⟨t, ht⟩ := exists_full_interior_patch K hK hU hne hUK
  let W₁ := U ∩ interior (convexHull ℝ (t.val : Set E))
  have hW₁ : IsOpen W₁ := hU.inter isOpen_interior
  have hW₁s : W₁ ⊆ h.source := fun _ hy => hUs hy.1
  have himage : IsOpen (h '' W₁) := h.isOpen_image_of_subset_source hW₁ hW₁s
  have hsubL : h '' W₁ ⊆ L.space := by
    rintro _ ⟨y, hy, rfl⟩
    exact hVL (hUV hy.1)
  obtain ⟨u, hu⟩ := exists_full_interior_patch L hL himage (ht.image h) hsubL
  let W₂ := W₁ ∩ (h.source ∩ h ⁻¹' interior (convexHull ℝ (u.val : Set E)))
  have hW₂ : IsOpen W₂ := hW₁.inter (h.isOpen_inter_preimage isOpen_interior)
  have hW₂ne : W₂.Nonempty := by
    obtain ⟨_, ⟨y, hy, rfl⟩, huy⟩ := hu
    exact ⟨y, hy, hW₁s hy, huy⟩
  have hW₂M : W₂ ⊆ M.space := fun _ hy => hUM hy.1.1
  obtain ⟨v, hv⟩ := exists_full_interior_patch M hM hW₂ hW₂ne hW₂M
  let W := W₂ ∩ interior (convexHull ℝ (v.val : Set E))
  have hW : IsOpen W := hW₂.inter isOpen_interior
  have huV : (convexHull ℝ (u.val : Set E) ∩ V).Nonempty := by
    obtain ⟨z, hzu, y, hy, hyz⟩ := u.property.2.2
    exact ⟨z, hzu, hyz ▸ hUV hy.1⟩
  have hvU : (convexHull ℝ (v.val : Set E) ∩ U).Nonempty := by
    obtain ⟨y, hyv, hy⟩ := v.property.2.2
    exact ⟨y, hyv, hy.1.1⟩
  let u' : L.FullFaceIn V := ⟨u.val, u.property.1, u.property.2.1, huV⟩
  let v' : M.FullFaceIn U := ⟨v.val, v.property.1, v.property.2.1, hvU⟩
  obtain ⟨A, hA⟩ := hf t.val t.property.1
  obtain ⟨B, hB⟩ := hg u.val u.property.1
  obtain ⟨C, hC⟩ := hcomp v.val v.property.1
  have hCAB : C = B.comp A := by
    apply ContinuousAffineMap.toAffineMap_injective
    apply AffineMap.ext_on (hW.affineSpan_eq_top hv)
    intro y hy
    change C y = B (A y)
    calc
      C y = k (h y) := (hC (interior_subset hy.2)).symm
      _ = B (h y) := hB (interior_subset hy.1.2.2)
      _ = B (A y) := congrArg B (hA (interior_subset hy.1.1.2))
  refine ⟨t, u', v', A, B, C, W, hA, hB, hC, hW, hv, ?_, ?_, ?_, ?_, ?_, hCAB⟩
  · exact fun _ hy => hy.1.1.1
  · exact fun _ hy => ⟨hUs hy.1.1.1, hVs (hUV hy.1.1.1)⟩
  · exact fun _ hy => hy.1.1.2
  · exact fun _ hy => hy.1.2.2
  · exact fun _ hy => hy.2

end Geometry
