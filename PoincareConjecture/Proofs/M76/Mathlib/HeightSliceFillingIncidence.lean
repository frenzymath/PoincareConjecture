import PoincareConjecture.Proofs.M76.Mathlib.AffinePlaneRectangleIncidence
import PoincareConjecture.Proofs.M76.Mathlib.HeightBoxGeometry










set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace HeightBox

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem filling_inter_slice_eq_side
    {f : ((ℝ × ℝ) × ℝ) → E} {r c t : ℝ} (hr : 0 < r)
    (hf : FinitePiecewiseAffineOn f (box r)) (hinj : InjOn f (box r))
    (ht : t ∈ Icc (-r) r) (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0)
    (hdim : Module.finrank ℝ E = 3)
    (hheight : ∀ p ∈ box r, A (f p) = c + p.1.1)
    {S d : Set E} (hplane : ∀ p ∈ box r, f p ∈ S ↔ p.2 = 0)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d (S ∩ {x | A x = c + t}))
    (hdplane : d ⊆ {x | A x = c + t}) :
    d ∩ (f '' slice r (-r) r t) = f '' slice r (-r) 0 t ∨
      d ∩ (f '' slice r (-r) r t) = f '' slice r 0 r t := by
  have hmap : MapsTo (sliceMap t) (base r) (box r) :=
    fun _ hx => ⟨⟨ht, hx.1⟩, hx.2⟩
  have hcopy := base_ballPair hr
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hcopy
  have hslice : FinitePiecewiseAffineOn (sliceMap t) (base r) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine (sliceMap t)⟩
  have hcomp : FinitePiecewiseAffineOn (f ∘ sliceMap t) (base r) := hf.comp hslice hmap
  have hcompinj : InjOn (f ∘ sliceMap t) (base r) := by
    intro x hx y hy heq
    exact sliceMap_injective t (hinj (hmap hx) (hmap hy) heq)
  let B := A - AffineMap.const ℝ E (c + t)
  have hB : B.linear ≠ 0 := by simpa [B] using hA
  have hdB : d ⊆ {x | B x = 0} := by
    intro x hx
    change A x - (c + t) = 0
    rw [hdplane hx, sub_self]
  have hfB : MapsTo (f ∘ sliceMap t) (base r) {x | B x = 0} := by
    intro x hx
    change A (f (sliceMap t x)) - (c + t) = 0
    rw [hheight _ (hmap hx)]
    exact sub_self (c + t)
  have hrim : ∀ x ∈ base r,
      (f ∘ sliceMap t) x ∈ S ∩ {x | A x = c + t} ↔ x.2 = 0 := by
    intro x hx
    constructor
    · intro hxq
      exact (hplane _ (hmap hx)).mp hxq.1
    · intro hx0
      exact ⟨(hplane _ (hmap hx)).mpr hx0, hheight _ (hmap hx)⟩
  have hresult := hcomp.inter_image_rectangle_eq_half_in_plane hr hcompinj
    hd B hB hdim hdB hfB hrim
  have himage (a b : ℝ) :
      (f ∘ sliceMap t) '' (Icc (-r) r ×ˢ Icc a b) = f '' slice r a b t := by
    calc
      (f ∘ sliceMap t) '' (Icc (-r) r ×ˢ Icc a b) =
          f '' (sliceMap t '' rectangle r a b) :=
        (image_image f (sliceMap t) (rectangle r a b)).symm
      _ = f '' slice r a b t := congrArg (f '' ·) (sliceMap_image r a b t)
  simpa only [base, himage] using hresult

end HeightBox
