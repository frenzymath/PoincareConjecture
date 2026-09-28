import PoincareConjecture.Proofs.M76.Mathlib.CoordinateHalfBoxes
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoordinates

set_option autoImplicit false

open Set Geometry

namespace HeightBox

def rectangle (r a b : ℝ) : Set (ℝ × ℝ) := Icc (-r) r ×ˢ Icc a b

def rectangleBoundary (r a b : ℝ) : Set (ℝ × ℝ) :=
  ({-r, r} ×ˢ Icc a b) ∪ (Icc (-r) r ×ˢ {a, b})

theorem rectangle_ballPair {r a b : ℝ} (hr : 0 < r) (hab : a < b) :
    IsFinitePLBallPair (ℝ × ℝ) (rectangle r a b) (rectangleBoundary r a b) :=
  (isFinitePLBallPair_Icc (show -r < r by linarith)).prod (isFinitePLBallPair_Icc hab)

noncomputable def trackCoordinates : ((ℝ × ℝ) × ℝ) ≃L[ℝ] ((ℝ × ℝ) × ℝ) :=
  (ContinuousLinearEquiv.prodComm ℝ (ℝ × ℝ) ℝ).trans
    (ContinuousLinearEquiv.prodAssoc ℝ ℝ ℝ ℝ).symm

theorem trackCoordinates_apply (p : (ℝ × ℝ) × ℝ) :
    trackCoordinates p = ((p.2, p.1.1), p.1.2) := rfl

theorem trackCoordinates_image (r a b : ℝ) :
    trackCoordinates '' (rectangle r a b ×ˢ Icc (-r) r) =
      CoordinateHalfBoxes.base r ×ˢ Icc a b := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨hq.2, hq.1.1⟩, hq.1.2⟩
  · rintro ⟨hp, hpz⟩
    exact ⟨((p.1.2, p.2), p.1.1), ⟨⟨hp.2, hpz⟩, hp.1⟩, rfl⟩

noncomputable def sliceMap (t : ℝ) : (ℝ × ℝ) →ᴬ[ℝ] ((ℝ × ℝ) × ℝ) :=
  ((ContinuousAffineMap.const ℝ (ℝ × ℝ) t).prod
    (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap

theorem sliceMap_injective (t : ℝ) : Function.Injective (sliceMap t) := by
  intro x y h
  exact Prod.ext (congrArg (fun p : (ℝ × ℝ) × ℝ => p.1.2) h)
    (congrArg (fun p : (ℝ × ℝ) × ℝ => p.2) h)

def slice (r a b t : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  ({t} ×ˢ Icc (-r) r) ×ˢ Icc a b

def sliceBoundary (r a b t : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  sliceMap t '' rectangleBoundary r a b

theorem sliceMap_image (r a b t : ℝ) :
    sliceMap t '' rectangle r a b = slice r a b t := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨rfl, hq.1⟩, hq.2⟩
  · rintro ⟨⟨hp, hs⟩, hz⟩
    refine ⟨(p.1.2, p.2), ⟨hs, hz⟩, ?_⟩
    exact Prod.ext (Prod.ext hp.symm rfl) rfl

theorem slice_ballPair {r a b : ℝ} (hr : 0 < r) (hab : a < b) (t : ℝ) :
    IsFinitePLBallPair (ℝ × ℝ) (slice r a b t) (sliceBoundary r a b t) := by
  have h := (rectangle_ballPair hr hab).affine_image (sliceMap t)
    (sliceMap_injective t).injOn
  rwa [sliceMap_image] at h

theorem slice_subset_box {r a b t : ℝ} (ha : -r ≤ a) (hb : b ≤ r)
    (ht : t ∈ Icc (-r) r) : slice r a b t ⊆ CoordinateHalfBoxes.box r := by
  rintro p ⟨⟨hp, hs⟩, hz⟩
  exact ⟨⟨hp.symm ▸ ht, hs⟩, ha.trans hz.1, hz.2.trans hb⟩

end HeightBox
