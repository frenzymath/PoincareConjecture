import PoincareConjecture.Proofs.M76.Mathlib.LongitudinalPrismCoordinates












set_option autoImplicit false

open Set CoordinateHalfBoxes

namespace CoordinateHalfBoxes





theorem longitudinalPrismCoordinates_restrict {r R : ℝ}
    (hr : r ≠ 0) (hR : R ≠ 0) (a b : ℝ) (x : (ℝ × ℝ) × ℝ) :
    longitudinalPrismCoordinates R a b (longitudinalPrismCoordinates r (-R) R x) =
      longitudinalPrismCoordinates r a b x := by
  simp only [longitudinalPrismCoordinates_apply]
  refine Prod.ext (Prod.ext rfl ?_) rfl
  field_simp [hr, hR]
  <;> ring

end CoordinateHalfBoxes

namespace OpenPartialHomeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]






theorem restrict_fixed_lateral_inverse_box
    (H : OpenPartialHomeomorph E ((ℝ × ℝ) × ℝ))
    {r R a b : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R) (hab : a < b)
    (F : ((ℝ × ℝ) × ℝ) → E)
    (hF : F = H.symm ∘ longitudinalPrismCoordinates R a b)
    (hsource : F '' box R ⊆ H.source)
    (hforward : ∀ x ∈ box R, H (F x) = longitudinalPrismCoordinates R a b x) :
    let G := F ∘ longitudinalPrismCoordinates r (-R) R
    G = H.symm ∘ longitudinalPrismCoordinates r a b ∧
      G '' box r = F '' ((Icc (-r) r ×ˢ Icc (-R) R) ×ˢ Icc (-r) r) ∧
      G '' box r = H.symm '' ((Icc (-r) r ×ˢ Icc a b) ×ˢ Icc (-r) r) ∧
      G '' box r ⊆ H.source ∧
      (Icc (-r) r ×ˢ Icc a b) ×ˢ Icc (-r) r ⊆ H.target ∧
      ∀ x ∈ box r, H (G x) = longitudinalPrismCoordinates r a b x := by
  let M := longitudinalPrismCoordinates r (-R) R
  let G := F ∘ M
  have hMimage : M '' box r =
      (Icc (-r) r ×ˢ Icc (-R) R) ×ˢ Icc (-r) r :=
    (longitudinalPrismCoordinates_properties hr (show -R < R by linarith)).2.1
  have hNimage := (longitudinalPrismCoordinates_properties hr hab).2.1
  have hinterval : Icc (-r) r ⊆ Icc (-R) R := by
    intro x hx
    exact ⟨(neg_le_neg hrR).trans hx.1, hx.2.trans hrR⟩
  have hmap (x : (ℝ × ℝ) × ℝ) (hx : x ∈ box r) : M x ∈ box R := by
    have hm := hMimage.subset (mem_image_of_mem M hx)
    exact ⟨⟨hinterval hm.1.1, hm.1.2⟩, hinterval hm.2⟩
  have hGsource : G '' box r ⊆ H.source := by
    rintro _ ⟨x, hx, rfl⟩
    exact hsource ⟨M x, hmap x hx, rfl⟩
  have hGforward (x : (ℝ × ℝ) × ℝ) (hx : x ∈ box r) :
      H (G x) = longitudinalPrismCoordinates r a b x := by
    change H (F (M x)) = _
    rw [hforward (M x) (hmap x hx)]
    exact longitudinalPrismCoordinates_restrict hr.ne' hR.ne' a b x
  have hGeq : G = H.symm ∘ longitudinalPrismCoordinates r a b := by
    funext x
    change F (M x) = H.symm (longitudinalPrismCoordinates r a b x)
    rw [hF, Function.comp_apply]
    exact congrArg H.symm (longitudinalPrismCoordinates_restrict hr.ne' hR.ne' a b x)
  have hGold : G '' box r =
      F '' ((Icc (-r) r ×ˢ Icc (-R) R) ×ˢ Icc (-r) r) := by
    calc
      G '' box r = F '' (M '' box r) := (image_image F M (box r)).symm
      _ = _ := congrArg (F '' ·) hMimage
  have hGnew : G '' box r =
      H.symm '' ((Icc (-r) r ×ˢ Icc a b) ×ˢ Icc (-r) r) := by
    rw [hGeq]
    calc
      (H.symm ∘ longitudinalPrismCoordinates r a b) '' box r =
          H.symm '' (longitudinalPrismCoordinates r a b '' box r) :=
        (image_image H.symm (longitudinalPrismCoordinates r a b) (box r)).symm
      _ = _ := congrArg (H.symm '' ·) hNimage
  have htarget : (Icc (-r) r ×ˢ Icc a b) ×ˢ Icc (-r) r ⊆ H.target := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hNimage.symm.subset hy
    rw [← hxy, ← hGforward x hx]
    exact H.map_source (hGsource (mem_image_of_mem G hx))
  exact ⟨hGeq, hGold, hGnew, hGsource, htarget, hGforward⟩

end OpenPartialHomeomorph
