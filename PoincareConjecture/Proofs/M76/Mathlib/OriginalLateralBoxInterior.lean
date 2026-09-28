import PoincareConjecture.Proofs.M76.Triangulation.OriginalLateralBoxUnion
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior

set_option autoImplicit false

open Set CoordinateHalfBoxes

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem original_cut_mem_interior_box_union
    (F₀ F₁ : ((ℝ × ℝ) × ℝ) → E)
    (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) {r : ℝ} (hr : 0 < r)
    (hF₀ : FinitePiecewiseAffineOn F₀ (box r))
    (hF₁ : FinitePiecewiseAffineOn F₁ (box r))
    (hinj₀ : InjOn F₀ (box r)) (hinj₁ : InjOn F₁ (box r))
    (hlateral₀ : ∀ t z, t ∈ Icc (-r) r → z ∈ Icc (-r) r →
      F₀ ((t, r), z) = f ((t, 0), z))
    (hlateral₁ : ∀ t z, t ∈ Icc (-r) r → z ∈ Icc (-r) r →
      F₁ ((t, -r), z) = f ((t, 0), z))
    (hcontact : (F₀ '' box r) ∩ (F₁ '' box r) =
      f '' ((Icc (-r) r ×ˢ {0}) ×ˢ Icc (-r) r)) :
    f 0 ∈ interior ((F₀ '' box r) ∪ (F₁ '' box r)) := by
  let d := f '' ((Icc (-r) r ×ˢ {0}) ×ˢ Icc (-r) r)
  let q := f '' ((({-r, r} ×ˢ {0}) ×ˢ Icc (-r) r) ∪
    ((Icc (-r) r ×ˢ {0}) ×ˢ {-r, r}))
  have hball := union_original_lateral_box_ballPair F₀ F₁ f hr
    hF₀ hF₁ hinj₀ hinj₁ hlateral₀ hlateral₁ hcontact
  change IsFinitePLBallPair ((ℝ × ℝ) × ℝ) ((F₀ '' box r) ∪ (F₁ '' box r))
    (((F₀ '' boxBoundary r) \ (d \ q)) ∪
      ((F₁ '' boxBoundary r) \ (d \ q))) at hball
  have hzero : (0 : ℝ) ∈ Icc (-r) r := ⟨neg_nonpos.mpr hr.le, hr.le⟩
  have hzeroNot : (0 : ℝ) ∉ ({-r, r} : Set ℝ) := by
    simp only [mem_insert_iff, mem_singleton_iff]
    rintro (h | h) <;> linarith
  have hd : f 0 ∈ d := ⟨0, ⟨⟨hzero, rfl⟩, hzero⟩, rfl⟩
  have hq : f 0 ∉ q := by
    rintro ⟨x, hx, hfx⟩
    have hxzero : x = 0 := f.injective hfx
    subst x
    rcases hx with hx | hx
    · exact hzeroNot hx.1.1
    · exact hzeroNot hx.2
  rw [hball.interior_eq_sdiff_of_finrank_eq f.linear.finrank_eq]
  refine ⟨Or.inl ⟨((0, r), 0), ⟨⟨hzero, by constructor <;> linarith⟩, hzero⟩,
    hlateral₀ 0 0 hzero hzero⟩, ?_⟩
  rintro (h | h)
  · exact h.2 ⟨hd, hq⟩
  · exact h.2 ⟨hd, hq⟩

end Geometry
