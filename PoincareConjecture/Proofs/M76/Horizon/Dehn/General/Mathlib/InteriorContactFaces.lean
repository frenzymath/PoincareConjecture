import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcSurgeryCrossings









set_option autoImplicit false

open Set Metric Geometry Topology unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)



theorem zero_face_card_le_two
    (K : SimplicialComplex ℝ V3) (hK : K.faces.Finite)
    {q : V3 → P2} (hq : K.AffineOnFaces q) (hi : InjOn q K.space)
    (ell : V3 →L[ℝ] ℝ) {face : Finset V3} (hf : face ∈ K.faces)
    (hzero : ∀ v ∈ face, ell v = 0) {p : V3}
    (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (face : Set V3)))
    (hpos : p ∈ closure (K.space ∩ {x | 0 < ell x})) : face.card ≤ 2 := by
  have hbound (s : Finset V3) (hs : s ∈ K.faces) : s.card ≤ 3 := by
    simpa [Module.finrank_prod] using hq.face_card_le_of_injOn hi hs
  by_contra hnot
  have hcard : face.card = 3 := by have := hbound face hf; omega
  have hmax : ∀ s ∈ K.faces, face ⊆ s → s = face := by
    intro s hs hfs
    exact (Finset.eq_of_subset_of_card_le hfs (by simpa [hcard] using hbound s hs)).symm
  obtain ⟨U, hU, hpU, hKU⟩ := K.exists_open_maximal_face_affine_germ hK hf hmax hp
  obtain ⟨x, hxU, hxK, hxpos⟩ := mem_closure_iff.mp hpos U hU hpU
  have hspan : affineSpan ℝ (face : Set V3) ≤ ell.ker.toAffineSubspace :=
    affineSpan_le.mpr hzero
  have hxzero : ell x = 0 := hspan ((hKU x hxU).mp hxK)
  exact hxpos.ne' hxzero




theorem exists_protected_motion_interior_contact_cases
    (J K K₀ : SimplicialComplex ℝ V3) (hK : K.faces.Finite)
    {P₀ : Set V3} {ε : ℝ} (hprotected : K₀.space = P₀)
    (q : V3 → P2) (hq : K.AffineOnFaces q) (hi : InjOn q K.space)
    (hint : ∀ x ∈ K.space, x ∈ interior J.space → q x ∈ interior (q '' K.space))
    (ell : V3 →L[ℝ] ℝ) (H : PLCarrierMotion J.space P₀ ε)
    (hH : K.AffineOnFaces (H.map 1))
    (hzero : ∀ face ∈ K.faces, (∀ v ∈ face, ell (H.map 1 v) = 0) →
      face ∈ K₀.faces ∧ ∀ v ∈ face, ell v = 0)
    (happroach : ∀ p ∈ P₀, p ∈ interior J.space → ell p = 0 →
      p ∈ closure (K.space ∩ {x | 0 < ell x})) :
    ∃ A : SimplicialComplex ℝ V3,
      A.faces.Finite ∧ A.space = H.map 1 '' K.space ∧
      ∀ p ∈ A.space, p ∈ interior J.space → ell p = 0 →
        (p ∈ K₀.vertices) ∨
        (∃ edge ∈ K₀.faces, edge.card = 2 ∧ (∀ v ∈ edge, ell v = 0) ∧
          p ∈ intrinsicInterior ℝ (convexHull ℝ (edge : Set V3))) ∨
        ∀ O : Set V3, IsOpen O → p ∈ O →
          ∃ T : OpenPartialHomeomorph V3 C3,
            p ∈ T.source ∧ T.source ⊆ O ∧ T p = 0 ∧
            LocallyPiecewiseAffineOn T T.source ∧
            LocallyPiecewiseAffineOn T.symm T.target ∧
            (∀ x ∈ T.source, x ∈ A.space ↔ (T x).1.1 = 0) ∧
            ∀ x ∈ T.source, ell x = (T x).2 := by
  classical
  have hHi : InjOn (H.map 1) K.space := (H.map 1).injective.injOn
  let A := hH.embeddedImage hHi
  have hA : A.faces.Finite := hH.embeddedImage_finite hHi hK
  have hAs : A.space = H.map 1 '' K.space := hH.embeddedImage_space hHi
  have hleft : LeftInvOn (H.map 1).symm (H.map 1) K.space :=
    fun x _ ↦ (H.map 1).symm_apply_apply x
  have hparam := hH.comp_inverse_on_embeddedImage hq hHi hleft
  have hparami := hH.injOn_comp_inverse_on_embeddedImage hHi hi hleft
  have hparamimage : (q ∘ (H.map 1).symm) '' A.space = q '' K.space := by
    rw [hAs, image_image]
    congr 1
    funext x
    exact congrArg q ((H.map 1).symm_apply_apply x)
  refine ⟨A, hA, hAs, ?_⟩
  intro p hp hpJ hpzero
  let x := (H.map 1).symm p
  have hxK : x ∈ K.space := by
    obtain ⟨y, hy, rfl⟩ := hAs.subset hp
    simpa only [x, (H.map 1).symm_apply_apply] using hy
  have hxp : H.map 1 x = p := (H.map 1).apply_symm_apply p
  have hxJ : x ∈ interior J.space := by
    have hinterior : H.map 1 '' interior J.space = interior J.space :=
      ((H.map 1).image_interior J.space).trans (congrArg interior (H.carrier 1))
    obtain ⟨y, hy, hyp⟩ := hinterior.symm.subset hpJ
    have hxy : x = y := (H.map 1).injective (hxp.trans hyp.symm)
    exact hxy.symm ▸ hy
  obtain ⟨face, hf, hxf⟩ := K.exists_face_intrinsicInterior_of_finite hK hxK
  by_cases hz : ∀ v ∈ face, ell (H.map 1 v) = 0
  · obtain ⟨hf₀, hfzero⟩ := hzero face hf hz
    have hxP₀ : x ∈ P₀ := hprotected.subset
      (K₀.convexHull_subset_space hf₀ (intrinsicInterior_subset hxf))
    have hfix : x = p := (H.fixed_protected 1 x hxP₀).symm.trans hxp
    have hcard := zero_face_card_le_two K hK hq hi ell hf hfzero hxf
      (happroach x hxP₀ hxJ (hfix ▸ hpzero))
    have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces hf)
    by_cases hone : face.card = 1
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hone
      have hxv : x = v := by
        simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using
          intrinsicInterior_subset hxf
      exact Or.inl (hfix ▸ hxv.symm ▸ K₀.face_subset_vertices hf₀ (Finset.mem_singleton_self v))
    · exact Or.inr (Or.inl ⟨face, hf₀, by omega, hfzero, hfix ▸ hxf⟩)
  · right; right
    intro O hO hpO
    have hfree (s : Finset V3) (hs : s ∈ A.faces)
        (hps : p ∈ convexHull ℝ (s : Set V3)) : ∃ v ∈ s, ell v ≠ 0 := by
      change s ∈ (hH.embeddedImage hHi).faces at hs
      rw [hH.embeddedImage_faces hHi] at hs
      obtain ⟨t, ht, rfl⟩ := hs
      rw [Finset.coe_image, ← hH.image_convexHull ht] at hps
      obtain ⟨y, hyt, hyp⟩ := hps
      have hxy : x = y := (H.map 1).injective (hxp.trans hyp.symm)
      have hft := K.subset_of_mem_intrinsicInterior_face hf ht hxf (hxy.symm ▸ hyt)
      push Not at hz
      obtain ⟨v, hv, hvzero⟩ := hz
      exact ⟨H.map 1 v, Finset.mem_image.mpr ⟨v, hft hv, rfl⟩, hvzero⟩
    have hparamint : (q ∘ (H.map 1).symm) p ∈
        interior ((q ∘ (H.map 1).symm) '' A.space) := by
      rw [hparamimage]
      exact hint x hxK hxJ
    exact exists_carrier_height_crossing A hA hparam hparami ell hp hpzero
      hparamint hfree hO hpO

end PoincareConjecture.M76.Dehn
