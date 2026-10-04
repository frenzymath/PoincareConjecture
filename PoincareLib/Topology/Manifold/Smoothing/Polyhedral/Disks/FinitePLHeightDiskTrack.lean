import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Levels.HeightBoxGeometry

/-!
# Complete planar disk tracks inside an actual height box

One finite PL embedding of the entire coordinate box transports
the two-dimensional slice disks and their full product track.
The original numerical height identifies every complete level
section, and the surface-plane formula identifies its exact
contact edge. See Alexander 1924, pp. 6--8 and derivation 280.
-/

set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace HeightBox

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A finite PL embedding of the full coordinate box gives a
joint finite PL product for every nondegenerate transverse
side rectangle. This is the literal inverse-chart track,
with no interpolation hypothesis. See derivation 280. -/
theorem exists_finitePL_disk_track {f : ((ℝ × ℝ) × ℝ) → E}
    {r a b : ℝ} (hr : 0 < r) (hab : a < b) (ha : -r ≤ a) (hb : b ≤ r)
    (hf : FinitePiecewiseAffineOn f (box r)) (hinj : InjOn f (box r)) :
    ∃ H : (rectangle r a b ×ˢ Icc (-r) r : Set ((ℝ × ℝ) × ℝ)) ≃ₜ
        (f '' (base r ×ˢ Icc a b)),
      H.IsFinitePL ∧ ∀ p, (H p : E) = f (trackCoordinates p) := by
  let S := rectangle r a b ×ˢ Icc (-r) r
  have hcoord (p : (ℝ × ℝ) × ℝ) (hp : p ∈ S) : trackCoordinates p ∈ box r :=
    ⟨⟨hp.2, hp.1.1⟩, ha.trans hp.1.2.1, hp.1.2.2.trans hb⟩
  have hpair := (rectangle_ballPair hr hab).prod
    (isFinitePLBallPair_Icc (show -r < r by linarith))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hpair
  have htrack : FinitePiecewiseAffineOn (f ∘ trackCoordinates) S := by
    have h := hf.precomp_affineEquiv trackCoordinates.toContinuousAffineEquiv
    dsimp only [S]
    rw [← hKs]
    apply h.restrict K hK
    intro p hp
    exact ⟨trackCoordinates p, hcoord p (hKs.subset hp),
      trackCoordinates.symm_apply_apply p⟩
  have htrackinj : InjOn (f ∘ trackCoordinates) S := by
    intro p hp q hq heq
    exact trackCoordinates.injective (hinj (hcoord p hp) (hcoord q hq) heq)
  obtain ⟨H, hH, hHval⟩ := htrack.exists_homeomorph_image htrackinj
  have himage : (f ∘ trackCoordinates) '' S = f '' (base r ×ˢ Icc a b) := by
    calc
      (f ∘ trackCoordinates) '' S = f '' (trackCoordinates '' S) :=
        (image_image f trackCoordinates S).symm
      _ = f '' (base r ×ˢ Icc a b) := congrArg (f '' ·) (trackCoordinates_image r a b)
  refine ⟨H.trans (Homeomorph.setCongr himage), ?_, hHval⟩
  exact ⟨f ∘ trackCoordinates, htrack, hHval⟩

/-- The same full-box embedding transports each complete
side slice to a genuine planar disk, including both endpoint
heights. See Alexander pp. 6--8 and derivation 280. -/
theorem slice_image_ballPair {f : ((ℝ × ℝ) × ℝ) → E}
    {r a b t : ℝ} (hr : 0 < r) (hab : a < b) (ha : -r ≤ a) (hb : b ≤ r)
    (hf : FinitePiecewiseAffineOn f (box r)) (hinj : InjOn f (box r))
    (ht : t ∈ Icc (-r) r) :
    IsFinitePLBallPair (ℝ × ℝ) (f '' slice r a b t) (f '' sliceBoundary r a b t) :=
  (slice_ballPair hr hab t).image_of_subset hf (slice_subset_box ha hb ht) hinj

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Every numerical level of the complete side-box image is
exactly its prescribed slice image. The equality uses the
actual height of the same map. See M76 derivation 280. -/
theorem side_image_inter_height {f : ((ℝ × ℝ) × ℝ) → E}
    {r a b c t : ℝ} (ha : -r ≤ a) (hb : b ≤ r) (ht : t ∈ Icc (-r) r)
    (A : E → ℝ) (hheight : ∀ p ∈ box r, A (f p) = c + p.1.1) :
    (f '' (base r ×ˢ Icc a b)) ∩ {x | A x = c + t} = f '' slice r a b t := by
  ext x
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, hpt⟩
    have hpbox : p ∈ box r := ⟨hp.1, ha.trans hp.2.1, hp.2.2.trans hb⟩
    have hpt' : p.1.1 = t := by
      have h := (hheight p hpbox).symm.trans hpt
      exact add_left_cancel h
    exact ⟨p, ⟨⟨hpt', hp.1.2⟩, hp.2⟩, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    have hpbox := slice_subset_box ha hb ht hp
    refine ⟨⟨p, ⟨⟨hpbox.1.1, hp.1.2⟩, hp.2⟩, rfl⟩, ?_⟩
    exact (hheight p hpbox).trans (congrArg (c + ·) hp.1.1)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The full surface contact of each planar side disk is
precisely its complete central edge. The one chart identifies
the whole source surface, not just a chosen arc. See derivation 280. -/
theorem slice_image_inter_surface {f : ((ℝ × ℝ) × ℝ) → E}
    {r a b t : ℝ} (ha : -r ≤ a) (hb : b ≤ r) (ha0 : a ≤ 0) (hb0 : 0 ≤ b)
    (ht : t ∈ Icc (-r) r) {S : Set E}
    (hplane : ∀ p ∈ box r, f p ∈ S ↔ p.2 = 0) :
    (f '' slice r a b t) ∩ S = f '' slice r 0 0 t := by
  ext x
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, hpS⟩
    have hp0 := (hplane p (slice_subset_box ha hb ht hp)).mp hpS
    refine ⟨p, ⟨hp.1, ?_, ?_⟩, rfl⟩ <;> simp only [hp0, le_refl]
  · rintro ⟨p, hp, rfl⟩
    have hp0 : p.2 = 0 := le_antisymm hp.2.2 hp.2.1
    have hpside : p ∈ slice r a b t := by
      exact ⟨hp.1, hp0.symm ▸ ha0, hp0.symm ▸ hb0⟩
    exact ⟨⟨p, hpside, rfl⟩, (hplane p (slice_subset_box ha hb ht hpside)).mpr hp0⟩

end HeightBox
