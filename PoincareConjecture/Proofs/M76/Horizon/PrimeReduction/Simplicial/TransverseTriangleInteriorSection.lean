import PoincareConjecture.Proofs.M76.Mathlib.MaximalFaceAffineGerm
import PoincareConjecture.Proofs.M76.Mathlib.HeightPlaneAffineCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkDimension

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_transverse_triangle_interior_two_segment_germ
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3) (hdim : Module.finrank ℝ E = 3)
    {t : Finset E} (ht : t ∈ K.faces) (ht3 : t.card = 3)
    (A : E →ᵃ[ℝ] ℝ) {p : E}
    (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set E)))
    (hpzero : A p = 0) (hne : ∃ v ∈ t, A v ≠ 0) :
    ∃ u v : E, u ≠ p ∧ v ≠ p ∧ segment ℝ p u ∩ segment ℝ p v = {p} ∧
      ∀ᶠ x in 𝓝 p, x ∈ K.space ∩ {y | A y = 0} ↔
        x ∈ segment ℝ p u ∪ segment ℝ p v := by
  let P := affineSpan ℝ (t : Set E)
  have hpP : p ∈ P := convexHull_subset_affineSpan _ (intrinsicInterior_subset hp)
  have hAP : ∃ u ∈ P, ∃ v ∈ P, A u ≠ A v := by
    obtain ⟨v, hv, hAv⟩ := hne
    exact ⟨v, mem_affineSpan ℝ hv, p, hpP, by simpa only [hpzero] using hAv⟩
  obtain ⟨f, hf0, hfA, hfP⟩ := P.exists_centered_height_plane_coordinates hdim
    (K.finrank_faceDirection_of_card ht ht3) A hAP hpP
  obtain ⟨U, hU, hpU, hKU⟩ :=
    K.exists_open_eq_affineSpan_of_triangle_interior hK hbound ht ht3 hp
  let l : ℝ →ᵃ[ℝ] E := f.toAffineEquiv.toAffineMap.comp
    (((AffineMap.const ℝ ℝ (0 : ℝ)).prod (AffineMap.id ℝ ℝ)).prod
      (AffineMap.const ℝ ℝ (0 : ℝ)))
  have hl (r : ℝ) : l r = f ((0, r), 0) := rfl
  have hl0 : l 0 = p := hf0
  have hli : Function.Injective l := by
    intro r s hrs
    exact congrArg (fun x : (ℝ × ℝ) × ℝ => x.1.2) (f.injective hrs)
  have hpos : segment ℝ p (l 1) = l '' Icc (0 : ℝ) 1 := by
    rw [← hl0, ← image_segment, segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)]
  have hneg : segment ℝ p (l (-1)) = l '' Icc (-1 : ℝ) 0 := by
    rw [segment_symm, ← hl0, ← image_segment,
      segment_eq_Icc (by norm_num : (-1 : ℝ) ≤ 0)]
  have hinter : segment ℝ p (l 1) ∩ segment ℝ p (l (-1)) = {p} := by
    rw [hpos, hneg, ← image_inter hli]
    have hi : Icc (0 : ℝ) 1 ∩ Icc (-1 : ℝ) 0 = {0} := by
      ext r
      simp only [mem_inter_iff, mem_Icc, mem_singleton_iff]
      constructor
      · intro h
        exact le_antisymm h.2.2 h.1.1
      · rintro rfl
        norm_num
    rw [hi, image_singleton, hl0]
  have hnonzero (r : ℝ) (hr : r ≠ 0) : l r ≠ p := by
    intro h
    exact hr (hli (h.trans hl0.symm))
  let c : E → ℝ := fun x => (f.symm x).1.2
  have hc : Continuous c := (continuous_snd.comp continuous_fst).comp f.symm.continuous
  have hpc : c p = 0 := by
    change (f.symm p).1.2 = 0
    rw [← hf0, f.symm_apply_apply]
    rfl
  have hstrip : c ⁻¹' Ioo (-1 : ℝ) 1 ∈ 𝓝 p :=
    (isOpen_Ioo.preimage hc).mem_nhds (by simp only [mem_preimage, hpc, mem_Ioo]; norm_num)
  refine ⟨l 1, l (-1), hnonzero 1 (by norm_num), hnonzero (-1) (by norm_num), hinter, ?_⟩
  filter_upwards [hU.mem_nhds hpU, hstrip] with x hxU hxstrip
  have hxlocal : x ∈ K.space ↔ x ∈ P :=
    ⟨fun hx => (hKU.subset ⟨hx, hxU⟩).1, fun hx => (hKU.symm.subset ⟨hx, hxU⟩).1⟩
  constructor
  · rintro ⟨hxK, hxA⟩
    change A x = 0 at hxA
    have hz : (f.symm x).2 = 0 := (hfP (f.symm x)).mp (by
      simpa only [f.apply_symm_apply] using hxlocal.mp hxK)
    have ha : (f.symm x).1.1 = 0 := by
      have h := hfA (f.symm x)
      simpa only [f.apply_symm_apply, hpzero, zero_add, hxA] using h.symm
    have hlx : l (c x) = x := by
      rw [hl]
      have heq : ((0, c x), 0) = f.symm x := by
        apply Prod.ext
        · exact Prod.ext ha.symm rfl
        · exact hz.symm
      rw [heq, f.apply_symm_apply]
    rcases le_total 0 (c x) with hcx | hcx
    · apply Or.inl
      rw [hpos]
      exact ⟨c x, ⟨hcx, hxstrip.2.le⟩, hlx⟩
    · apply Or.inr
      rw [hneg]
      exact ⟨c x, ⟨hxstrip.1.le, hcx⟩, hlx⟩
  · intro hx
    have hxline : ∃ r : ℝ, l r = x := by
      rcases hx with hx | hx
      · obtain ⟨r, _, hr⟩ := hpos.subset hx
        exact ⟨r, hr⟩
      · obtain ⟨r, _, hr⟩ := hneg.subset hx
        exact ⟨r, hr⟩
    obtain ⟨r, hr⟩ := hxline
    have hxP : x ∈ P := by
      rw [← hr, hl]
      exact (hfP ((0, r), 0)).mpr rfl
    refine ⟨hxlocal.mpr hxP, ?_⟩
    change A x = 0
    rw [← hr, hl, hfA, hpzero]
    simp only [zero_add]

end Geometry.SimplicialComplex
