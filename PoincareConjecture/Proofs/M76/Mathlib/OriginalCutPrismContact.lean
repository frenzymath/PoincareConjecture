import PoincareConjecture.Proofs.M76.Mathlib.FixedLateralInversePrism

set_option autoImplicit false

open Set CoordinateHalfBoxes

namespace OpenPartialHomeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem inverse_original_cut_coordinates
    (H : OpenPartialHomeomorph E ((ℝ × ℝ) × ℝ))
    (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) {R c k : ℝ} (hk : 0 < k)
    (hforward : ∀ u ∈ box R,
      H (f u) = ((u.1.1, c + k * u.1.2), u.2))
    {y : (ℝ × ℝ) × ℝ} (hy : y ∈ H.target)
    (hcut : H.symm y ∈ f '' box R) :
    (f.symm (H.symm y)).1.1 = y.1.1 ∧
      (f.symm (H.symm y)).2 = y.2 ∧
      y.1.2 = c + k * (f.symm (H.symm y)).1.2 ∧
      (0 ≤ (f.symm (H.symm y)).1.2 ↔ c ≤ y.1.2) ∧
      ((f.symm (H.symm y)).1.2 ≤ 0 ↔ y.1.2 ≤ c) := by
  obtain ⟨u, hu, hfu⟩ := hcut
  have hcoord : f.symm (H.symm y) = u := by
    rw [← hfu, f.symm_apply_apply]
  have hvalue : ((u.1.1, c + k * u.1.2), u.2) = y :=
    (hforward u hu).symm.trans ((congrArg H hfu).trans (H.right_inv hy))
  have ht := congrArg (fun x : (ℝ × ℝ) × ℝ => x.1.1) hvalue
  change u.1.1 = y.1.1 at ht
  have hz := congrArg (fun x : (ℝ × ℝ) × ℝ => x.2) hvalue
  change u.2 = y.2 at hz
  have hs := congrArg (fun x : (ℝ × ℝ) × ℝ => x.1.2) hvalue
  change c + k * u.1.2 = y.1.2 at hs
  rw [hcoord]
  refine ⟨ht, hz, hs.symm, ?_, ?_⟩
  · constructor
    · intro h
      have hm := mul_nonneg hk.le h
      linarith
    · intro h
      exact nonneg_of_mul_nonneg_right (by linarith) hk
  · constructor
    · intro h
      have hm := mul_nonpos_of_nonneg_of_nonpos hk.le h
      linarith
    · intro h
      exact nonpos_of_mul_nonpos_right (by linarith) hk

theorem inverse_prisms_inter_eq_original_cut
    (H₀ H₁ : OpenPartialHomeomorph E ((ℝ × ℝ) × ℝ))
    (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) {r R a₀ b₀ a₁ b₁ k₀ k₁ : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hab₀ : a₀ ≤ b₀) (hab₁ : a₁ ≤ b₁)
    (hk₀ : 0 < k₀) (hk₁ : 0 < k₁)
    (hP₀ : (Icc (-r) r ×ˢ Icc a₀ b₀) ×ˢ Icc (-r) r ⊆ H₀.target)
    (hP₁ : (Icc (-r) r ×ˢ Icc a₁ b₁) ×ˢ Icc (-r) r ⊆ H₁.target)
    (hcut₀ : f '' box R ⊆ H₀.source) (hcut₁ : f '' box R ⊆ H₁.source)
    (hforward₀ : ∀ u ∈ box R,
      H₀ (f u) = ((u.1.1, b₀ + k₀ * u.1.2), u.2))
    (hforward₁ : ∀ u ∈ box R,
      H₁ (f u) = ((u.1.1, a₁ + k₁ * u.1.2), u.2))
    (hconfined :
      (H₀.symm '' ((Icc (-r) r ×ˢ Icc a₀ b₀) ×ˢ Icc (-r) r)) ∩
        (H₁.symm '' ((Icc (-r) r ×ˢ Icc a₁ b₁) ×ˢ Icc (-r) r)) ⊆ f '' box R) :
    (H₀.symm '' ((Icc (-r) r ×ˢ Icc a₀ b₀) ×ˢ Icc (-r) r)) ∩
      (H₁.symm '' ((Icc (-r) r ×ˢ Icc a₁ b₁) ×ˢ Icc (-r) r)) =
        f '' ((Icc (-r) r ×ˢ {0}) ×ˢ Icc (-r) r) := by
  have hinterval : Icc (-r) r ⊆ Icc (-R) R := by
    intro x hx
    exact ⟨(neg_le_neg hrR).trans hx.1, hx.2.trans hrR⟩
  ext x
  constructor
  · intro hx
    have hxcut := hconfined hx
    obtain ⟨y₀, hy₀, hy₀x⟩ := hx.1
    obtain ⟨y₁, hy₁, hy₁x⟩ := hx.2
    have hc₀ := H₀.inverse_original_cut_coordinates f hk₀ hforward₀ (hP₀ hy₀)
      (hy₀x.symm ▸ hxcut)
    have hc₁ := H₁.inverse_original_cut_coordinates f hk₁ hforward₁ (hP₁ hy₁)
      (hy₁x.symm ▸ hxcut)
    rw [hy₀x] at hc₀
    rw [hy₁x] at hc₁
    have hs₀ : (f.symm x).1.2 ≤ 0 := hc₀.2.2.2.2.mpr hy₀.1.2.2
    have hs₁ : 0 ≤ (f.symm x).1.2 := hc₁.2.2.2.1.mpr hy₁.1.2.1
    have ht : (f.symm x).1.1 ∈ Icc (-r) r := hc₀.1.symm ▸ hy₀.1.1
    have hz : (f.symm x).2 ∈ Icc (-r) r := hc₀.2.1.symm ▸ hy₀.2
    exact ⟨f.symm x, ⟨⟨ht, le_antisymm hs₀ hs₁⟩, hz⟩, f.apply_symm_apply x⟩
  · rintro ⟨u, hu, rfl⟩
    have hs : u.1.2 = 0 := hu.1.2
    have hR : 0 ≤ R := hr.le.trans hrR
    have huR : u ∈ box R :=
      ⟨⟨hinterval hu.1.1, hs.symm ▸ ⟨neg_nonpos.mpr hR, hR⟩⟩, hinterval hu.2⟩
    have hvalue₀ : H₀ (f u) = ((u.1.1, b₀), u.2) := by
      rw [hforward₀ u huR, hs, mul_zero, add_zero]
    have hvalue₁ : H₁ (f u) = ((u.1.1, a₁), u.2) := by
      rw [hforward₁ u huR, hs, mul_zero, add_zero]
    constructor
    · refine ⟨((u.1.1, b₀), u.2), ⟨⟨hu.1.1, hab₀, le_rfl⟩, hu.2⟩, ?_⟩
      rw [← hvalue₀]
      exact H₀.left_inv (hcut₀ ⟨u, huR, rfl⟩)
    · refine ⟨((u.1.1, a₁), u.2), ⟨⟨hu.1.1, le_rfl, hab₁⟩, hu.2⟩, ?_⟩
      rw [← hvalue₁]
      exact H₁.left_inv (hcut₁ ⟨u, huR, rfl⟩)

end OpenPartialHomeomorph
