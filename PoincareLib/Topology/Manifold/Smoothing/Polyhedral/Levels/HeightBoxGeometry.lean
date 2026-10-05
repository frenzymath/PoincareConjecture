import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.CoordinateHalfBoxes
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallImages
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.FinitePLCoordinates

/-!
# Coordinate disks and their complete height tracks

An affine coordinate permutation identifies a rectangle times
the height interval with the entire side box. The fixed-height
rectangles are genuine finite PL disks with their full rims.
See Alexander 1924, pp. 6--8, Hudson 1969, pp. 15--19 and
M76 derivation 280.
-/

set_option autoImplicit false

open Set Geometry

namespace HeightBox

/-- The transverse rectangle for a height track.
See M76 derivation 280. -/
def rectangle (r a b : ℝ) : Set (ℝ × ℝ) := Icc (-r) r ×ˢ Icc a b

/-- The entire boundary of the transverse rectangle.
See M76 derivation 280. -/
def rectangleBoundary (r a b : ℝ) : Set (ℝ × ℝ) :=
  ({-r, r} ×ˢ Icc a b) ∪ (Icc (-r) r ×ˢ {a, b})

/-- The transverse rectangle is an actual two-dimensional
finite PL ball when both intervals have positive length.
See Hudson pp. 15--19 and M76 derivation 280. -/
theorem rectangle_ballPair {r a b : ℝ} (hr : 0 < r) (hab : a < b) :
    IsFinitePLBallPair (ℝ × ℝ) (rectangle r a b) (rectangleBoundary r a b) :=
  (isFinitePLBallPair_Icc (show -r < r by linarith)).prod (isFinitePLBallPair_Icc hab)

/-- Put the last, height, coordinate first, retaining the
two transverse coordinates literally. See derivation 280. -/
noncomputable def trackCoordinates : ((ℝ × ℝ) × ℝ) ≃L[ℝ] ((ℝ × ℝ) × ℝ) :=
  (ContinuousLinearEquiv.prodComm ℝ (ℝ × ℝ) ℝ).trans
    (ContinuousLinearEquiv.prodAssoc ℝ ℝ ℝ ℝ).symm

/-- The full numerical coordinate formula of the track.
See M76 derivation 280. -/
theorem trackCoordinates_apply (p : (ℝ × ℝ) × ℝ) :
    trackCoordinates p = ((p.2, p.1.1), p.1.2) := rfl

/-- The permuted product is the whole coordinate side box.
See Alexander pp. 6--8 and M76 derivation 280. -/
theorem trackCoordinates_image (r a b : ℝ) :
    trackCoordinates '' (rectangle r a b ×ˢ Icc (-r) r) =
      CoordinateHalfBoxes.base r ×ˢ Icc a b := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨hq.2, hq.1.1⟩, hq.1.2⟩
  · rintro ⟨hp, hpz⟩
    exact ⟨((p.1.2, p.2), p.1.1), ⟨⟨hp.2, hpz⟩, hp.1⟩, rfl⟩

/-- The affine inclusion of a transverse rectangle at the
literal prescribed height. See M76 derivation 280. -/
noncomputable def sliceMap (t : ℝ) : (ℝ × ℝ) →ᴬ[ℝ] ((ℝ × ℝ) × ℝ) :=
  ((ContinuousAffineMap.const ℝ (ℝ × ℝ) t).prod
    (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap

/-- A fixed-height slice retains both transverse coordinates.
See M76 derivation 280. -/
theorem sliceMap_injective (t : ℝ) : Function.Injective (sliceMap t) := by
  intro x y h
  exact Prod.ext (congrArg (fun p : (ℝ × ℝ) × ℝ => p.1.2) h)
    (congrArg (fun p : (ℝ × ℝ) × ℝ => p.2) h)

/-- The complete coordinate disk at height t.
See M76 derivation 280. -/
def slice (r a b t : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  ({t} ×ˢ Icc (-r) r) ×ˢ Icc a b

/-- The full rim of the coordinate disk at height t.
See M76 derivation 280. -/
def sliceBoundary (r a b t : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  sliceMap t '' rectangleBoundary r a b

/-- The affine slice inclusion covers exactly the full disk.
See M76 derivation 280. -/
theorem sliceMap_image (r a b t : ℝ) :
    sliceMap t '' rectangle r a b = slice r a b t := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨rfl, hq.1⟩, hq.2⟩
  · rintro ⟨⟨hp, hs⟩, hz⟩
    refine ⟨(p.1.2, p.2), ⟨hs, hz⟩, ?_⟩
    exact Prod.ext (Prod.ext hp.symm rfl) rfl

/-- Every complete slice, including endpoint slices, is an
actual finite PL disk with its stated rim. See derivation 280. -/
theorem slice_ballPair {r a b : ℝ} (hr : 0 < r) (hab : a < b) (t : ℝ) :
    IsFinitePLBallPair (ℝ × ℝ) (slice r a b t) (sliceBoundary r a b t) := by
  have h := (rectangle_ballPair hr hab).affine_image (sliceMap t)
    (sliceMap_injective t).injOn
  rwa [sliceMap_image] at h

/-- All level disks of a side box lie in the same full
coordinate box. See M76 derivation 280. -/
theorem slice_subset_box {r a b t : ℝ} (ha : -r ≤ a) (hb : b ≤ r)
    (ht : t ∈ Icc (-r) r) : slice r a b t ⊆ CoordinateHalfBoxes.box r := by
  rintro p ⟨⟨hp, hs⟩, hz⟩
  exact ⟨⟨hp.symm ▸ ht, hs⟩, ha.trans hz.1, hz.2.trans hb⟩

end HeightBox
