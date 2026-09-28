import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.InteriorContactFaces

set_option autoImplicit false

open Set Metric Geometry Topology unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem boundary_motion_interior_contact_cases
    (J K B : SimplicialComplex ℝ V3) (hK : K.faces.Finite)
    (q : V3 → V2) (hq : K.AffineOnFaces q) (hi : InjOn q K.space)
    (ell region : V3 →L[ℝ] ℝ)
    (hint : ∀ x ∈ K.space, x ∈ interior J.space → 0 < region x →
      q x ∈ interior (q '' K.space))
    {P₀ : Set V3} {ε : ℝ} (H : PLCarrierMotion J.space P₀ ε)
    (hH : K.AffineOnFaces (H.map 1))
    (hregion : ∀ x, region (H.map 1 x) = region x)
    (hzero : ∀ face ∈ K.faces, (∀ v ∈ face, ell (H.map 1 v) = 0) →
      ∀ v ∈ face, ell v = 0)
    (hfaces : B.faces = (fun face ↦ face.image (H.map 1)) '' K.faces)
    (happroach : ∀ x ∈ K.space, x ∈ interior J.space → 0 < region x → ell x = 0 →
      x ∈ closure (K.space ∩ {y | 0 < ell y})) :
    ∀ p ∈ B.space, p ∈ interior J.space → 0 < region p → ell p = 0 →
      (∃ v ∈ K.vertices, ell v = 0 ∧ H.map 1 v = p) ∨
      (∃ edge ∈ K.faces, edge.card = 2 ∧ (∀ v ∈ edge, ell v = 0) ∧
        (∀ v ∈ edge, ell (H.map 1 v) = 0) ∧
        p ∈ H.map 1 '' intrinsicInterior ℝ (convexHull ℝ (edge : Set V3))) ∨
      ∀ O : Set V3, IsOpen O → p ∈ O →
        ∃ T : OpenPartialHomeomorph V3 C3,
          p ∈ T.source ∧ T.source ⊆ O ∧ T p = 0 ∧
          LocallyPiecewiseAffineOn T T.source ∧
          LocallyPiecewiseAffineOn T.symm T.target ∧
          (∀ x ∈ T.source, x ∈ B.space ↔ (T x).1.1 = 0) ∧
          ∀ x ∈ T.source, ell x = (T x).2 := by
  classical
  let c := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  have hcq : K.AffineOnFaces (c ∘ q) :=
    hq.postcomp c.toContinuousLinearMap.toContinuousAffineMap
  have hcqi : InjOn (c ∘ q) K.space := c.injective.comp_injOn hi
  have hcint (x : V3) (hx : x ∈ K.space) (hxJ : x ∈ interior J.space)
      (hxR : 0 < region x) : (c ∘ q) x ∈ interior ((c ∘ q) '' K.space) := by
    have h := c.toHomeomorph.image_interior (q '' K.space)
    change c '' interior (q '' K.space) = interior (c '' (q '' K.space)) at h
    have hm := mem_image_of_mem c (hint x hx hxJ hxR)
    rw [h] at hm
    simpa only [image_image, Function.comp_def] using hm
  have hHi : InjOn (H.map 1) K.space := (H.map 1).injective.injOn
  let A := hH.embeddedImage hHi
  have hBA : B = A := by
    apply SimplicialComplex.ext
    exact hfaces.trans (hH.embeddedImage_faces hHi).symm
  have hB : B.faces.Finite := hBA ▸ hH.embeddedImage_finite hHi hK
  have hBs : B.space = H.map 1 '' K.space :=
    (congrArg SimplicialComplex.space hBA).trans (hH.embeddedImage_space hHi)
  have hleft : LeftInvOn (H.map 1).symm (H.map 1) K.space :=
    fun x _ ↦ (H.map 1).symm_apply_apply x
  have hparam : B.AffineOnFaces ((c ∘ q) ∘ (H.map 1).symm) := by
    rw [hBA]
    exact hH.comp_inverse_on_embeddedImage hcq hHi hleft
  have hparami : InjOn ((c ∘ q) ∘ (H.map 1).symm) B.space := by
    rw [hBA]
    exact hH.injOn_comp_inverse_on_embeddedImage hHi hcqi hleft
  have hparamimage : ((c ∘ q) ∘ (H.map 1).symm) '' B.space = (c ∘ q) '' K.space := by
    rw [hBs, image_image]
    congr 1
    funext x
    exact congrArg (c ∘ q) ((H.map 1).symm_apply_apply x)
  intro p hp hpJ hpR hpzero
  let x := (H.map 1).symm p
  have hxK : x ∈ K.space := by
    obtain ⟨y, hy, rfl⟩ := hBs.subset hp
    simpa only [x, (H.map 1).symm_apply_apply] using hy
  have hxp : H.map 1 x = p := (H.map 1).apply_symm_apply p
  have hxJ : x ∈ interior J.space := by
    have hinterior : H.map 1 '' interior J.space = interior J.space :=
      ((H.map 1).image_interior J.space).trans (congrArg interior (H.carrier 1))
    obtain ⟨y, hy, hyp⟩ := hinterior.symm.subset hpJ
    exact ((H.map 1).injective (hxp.trans hyp.symm)).symm ▸ hy
  have hxR : 0 < region x := by rw [← hregion x, hxp]; exact hpR
  obtain ⟨face, hf, hxf⟩ := K.exists_face_intrinsicInterior_of_finite hK hxK
  by_cases hz : ∀ v ∈ face, ell (H.map 1 v) = 0
  · have hfzero := hzero face hf hz
    have hxzero : ell x = 0 := convexHull_min hfzero
      ((convex_singleton (0 : ℝ)).linear_preimage ell.toLinearMap) (intrinsicInterior_subset hxf)
    have hcard := zero_face_card_le_two K hK hcq hcqi ell hf hfzero hxf
      (happroach x hxK hxJ hxR hxzero)
    have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces hf)
    by_cases hone : face.card = 1
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hone
      have hxv : x = v := by
        simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using
          intrinsicInterior_subset hxf
      exact Or.inl ⟨v, K.face_subset_vertices hf (Finset.mem_singleton_self v),
        hfzero v (Finset.mem_singleton_self v), hxv ▸ hxp⟩
    · exact Or.inr (Or.inl ⟨face, hf, by omega, hfzero, hz, x, hxf, hxp⟩)
  · right; right
    intro O hO hpO
    have hfree (s : Finset V3) (hs : s ∈ B.faces)
        (hps : p ∈ convexHull ℝ (s : Set V3)) : ∃ v ∈ s, ell v ≠ 0 := by
      rw [hfaces] at hs
      obtain ⟨t, ht, rfl⟩ := hs
      rw [Finset.coe_image, ← hH.image_convexHull ht] at hps
      obtain ⟨y, hyt, hyp⟩ := hps
      have hxy : x = y := (H.map 1).injective (hxp.trans hyp.symm)
      have hft := K.subset_of_mem_intrinsicInterior_face hf ht hxf (hxy.symm ▸ hyt)
      push Not at hz
      obtain ⟨v, hv, hvzero⟩ := hz
      exact ⟨H.map 1 v, Finset.mem_image.mpr ⟨v, hft hv, rfl⟩, hvzero⟩
    have hparamint : ((c ∘ q) ∘ (H.map 1).symm) p ∈
        interior (((c ∘ q) ∘ (H.map 1).symm) '' B.space) := by
      rw [hparamimage]
      exact hcint x hxK hxJ hxR
    exact exists_carrier_height_crossing B hB hparam hparami ell hp hpzero
      hparamint hfree hO hpO

end PoincareConjecture.M76.Dehn
