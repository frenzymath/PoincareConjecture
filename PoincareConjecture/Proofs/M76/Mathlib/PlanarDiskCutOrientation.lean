import PoincareConjecture.Proofs.M76.Mathlib.CoordinateTransverseReflection
import PoincareConjecture.Proofs.M76.Mathlib.HeightSliceFillingIncidence












set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes HeightBox

namespace ContinuousAffineEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]







theorem exists_positive_transverse_planar_cut
    (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) {r c : ℝ} (hr : 0 < r)
    (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0) (hdim : Module.finrank ℝ E = 3)
    (hheight : ∀ x, A (f x) = c + x.1.1)
    {S d : Set E} (hsurface : ∀ x ∈ box r, f x ∈ S ↔ x.2 = 0)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d (S ∩ {x | A x = c}))
    (hdplane : d ⊆ {x | A x = c}) :
    ∃ g : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E,
      (g = f ∨ g = transverseReflection.toContinuousAffineEquiv.trans f) ∧
      g 0 = f 0 ∧ (∀ a, g '' box a = f '' box a) ∧
      (∀ x, A (g x) = c + x.1.1) ∧
      (∀ x ∈ box r, g x ∈ S ↔ x.2 = 0) ∧
      ∀ x ∈ box r, x.1.1 = 0 → (g x ∈ d ↔ 0 ≤ x.2) := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := box_ballPair hr
  have hf : FinitePiecewiseAffineOn f (box r) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine f.toContinuousAffineMap⟩
  have hside := filling_inter_slice_eq_side hr hf f.injective.injOn
    (show (0 : ℝ) ∈ Icc (-r) r from ⟨neg_nonpos.mpr hr.le, hr.le⟩)
    A hA hdim (fun x _ => hheight x) hsurface
    (by simpa only [add_zero] using hd) (by simpa only [add_zero] using hdplane)
  have hpoint {a b : ℝ}
      (heq : d ∩ (f '' slice r (-r) r 0) = f '' slice r a b 0)
      (x : (ℝ × ℝ) × ℝ) (hx : x ∈ box r) (hx0 : x.1.1 = 0) :
      f x ∈ d ↔ x.2 ∈ Icc a b := by
    have hxsl : x ∈ slice r (-r) r 0 := ⟨⟨hx0, hx.1.2⟩, hx.2⟩
    constructor
    · intro hxd
      obtain ⟨y, hy, hfy⟩ := heq.subset ⟨hxd, mem_image_of_mem f hxsl⟩
      have hyx : y = x := f.injective hfy
      exact hyx ▸ hy.2
    · intro hxside
      exact (heq.symm.subset ⟨x, ⟨⟨hx0, hx.1.2⟩, hxside⟩, rfl⟩).1
  rcases hside with hminus | hplus
  · let g := transverseReflection.toContinuousAffineEquiv.trans f
    have hgbox (x : (ℝ × ℝ) × ℝ) (hx : x ∈ box r) :
        transverseReflection x ∈ box r := (transverseReflection_mem_box r x).mpr hx
    refine ⟨g, Or.inr rfl, ?_, image_transverseReflection_trans f, ?_, ?_, ?_⟩
    · change f (transverseReflection 0) = f 0
      rw [transverseReflection_zero]
    · intro x
      exact hheight (transverseReflection x)
    · intro x hx
      change f (transverseReflection x) ∈ S ↔ x.2 = 0
      simpa only [transverseReflection_apply, neg_eq_zero] using
        hsurface (transverseReflection x) (hgbox x hx)
    · intro x hx hx0
      change f (transverseReflection x) ∈ d ↔ 0 ≤ x.2
      rw [hpoint hminus (transverseReflection x) (hgbox x hx) hx0]
      change (-r ≤ -x.2 ∧ -x.2 ≤ 0) ↔ 0 ≤ x.2
      constructor
      · intro h
        linarith [h.2]
      · intro h
        exact ⟨neg_le_neg hx.2.2, neg_nonpos.mpr h⟩
  · refine ⟨f, Or.inl rfl, rfl, fun _ => rfl, hheight, hsurface, ?_⟩
    intro x hx hx0
    rw [hpoint hplus x hx hx0]
    exact ⟨fun h => h.1, fun h => ⟨h, hx.2.2⟩⟩

end ContinuousAffineEquiv
