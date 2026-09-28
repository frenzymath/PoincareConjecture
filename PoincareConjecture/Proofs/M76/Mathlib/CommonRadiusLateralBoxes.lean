import PoincareConjecture.Proofs.M76.Mathlib.LongitudinalPrismCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.FinitePositiveHeightGap

set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace Geometry

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite ι]

theorem exists_common_radius_fixed_lateral_boxes
    (R : ι → ℝ) (hR : ∀ i, 0 < R i) (F : ι → ((ℝ × ℝ) × ℝ) → E)
    (hF : ∀ i, FinitePiecewiseAffineOn (F i) (box (R i)))
    (hinj : ∀ i, InjOn (F i) (box (R i)))
    (A : E → ℝ) (c : ℝ)
    (hheight : ∀ i x, x ∈ box (R i) → A (F i x) = c + x.1.1)
    {S : Set E} (hplane : ∀ i x, x ∈ box (R i) → (F i x ∈ S ↔ x.2 = 0))
    (f : ι → Bool → ((ℝ × ℝ) × ℝ) → E)
    (hlateral : ∀ i j t z, t ∈ Icc (-R i) (R i) → z ∈ Icc (-R i) (R i) →
      F i ((t, if j then R i else -R i), z) = f i j ((t, 0), z))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℝ) (G : ι → ((ℝ × ℝ) × ℝ) → E),
      r ∈ Ioo 0 ε ∧ (∀ i, r < R i) ∧
      ∀ i,
        G i = F i ∘ longitudinalPrismCoordinates r (-R i) (R i) ∧
        FinitePiecewiseAffineOn (G i) (box r) ∧ InjOn (G i) (box r) ∧
        G i '' box r = F i '' ((Icc (-r) r ×ˢ Icc (-R i) (R i)) ×ˢ Icc (-r) r) ∧
        G i '' box r ⊆ F i '' box (R i) ∧
        IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (G i '' box r) (G i '' boxBoundary r) ∧
        (∀ x ∈ box r, A (G i x) = c + x.1.1) ∧
        (∀ x ∈ box r, G i x ∈ S ↔ x.2 = 0) ∧
        ∀ j t z, t ∈ Icc (-r) r → z ∈ Icc (-r) r →
          G i ((t, if j then r else -r), z) = f i j ((t, 0), z) := by
  classical
  obtain ⟨r, hr, hsmall⟩ :=
    (Set.toFinite (univ : Set ι)).exists_pos_lt_positive_values R hε
  have hrR (i : ι) : r < R i := hsmall i (mem_univ i) (hR i)
  have hinterval (i : ι) : Icc (-r) r ⊆ Icc (-R i) (R i) := by
    intro x hx
    exact ⟨(neg_le_neg (hrR i).le).trans hx.1, hx.2.trans (hrR i).le⟩
  let N (i : ι) := longitudinalPrismCoordinates r (-R i) (R i)
  let G (i : ι) : ((ℝ × ℝ) × ℝ) → E := F i ∘ N i
  have hPsub (i : ι) :
      (Icc (-r) r ×ˢ Icc (-R i) (R i)) ×ˢ Icc (-r) r ⊆ box (R i) := by
    intro x hx
    exact ⟨⟨hinterval i hx.1.1, hx.1.2⟩, hinterval i hx.2⟩
  have hprops (i : ι) :=
    longitudinalPrismCoordinates_properties hr.1 (show -R i < R i by linarith [hR i])
  have hmap (i : ι) : MapsTo (N i) (box r) (box (R i)) := by
    intro x hx
    exact hPsub i ((hprops i).2.1.subset (mem_image_of_mem _ hx))
  have hcopy := box_ballPair hr.1
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hcopy
  have hN (i : ι) : FinitePiecewiseAffineOn (N i) (box r) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine (N i)⟩
  refine ⟨r, G, hr, hrR, ?_⟩
  intro i
  have hGi : FinitePiecewiseAffineOn (G i) (box r) := (hF i).comp (hN i) (hmap i)
  have hGinj : InjOn (G i) (box r) := by
    intro x hx y hy hxy
    exact (hprops i).1 ((hinj i) (hmap i hx) (hmap i hy) hxy)
  have hGimage : G i '' box r =
      F i '' ((Icc (-r) r ×ˢ Icc (-R i) (R i)) ×ˢ Icc (-r) r) := by
    change (F i ∘ N i) '' box r = _
    calc
      (F i ∘ N i) '' box r = F i '' (N i '' box r) :=
        (image_image (F i) (N i) (box r)).symm
      _ = _ := congrArg (F i '' ·) (hprops i).2.1
  refine ⟨rfl, hGi, hGinj, hGimage, ?_, (box_ballPair hr.1).image hGi hGinj,
    ?_, ?_, ?_⟩
  · rw [hGimage]
    exact image_mono (hPsub i)
  · intro x hx
    exact hheight i (N i x) (hmap i hx)
  · intro x hx
    exact hplane i (N i x) (hmap i hx)
  · intro j t z ht hz
    cases j
    · change F i (N i ((t, -r), z)) = f i false ((t, 0), z)
      rw [(hprops i).2.2.1]
      exact hlateral i false t z (hinterval i ht) (hinterval i hz)
    · change F i (N i ((t, r), z)) = f i true ((t, 0), z)
      rw [(hprops i).2.2.2]
      exact hlateral i true t z (hinterval i ht) (hinterval i hz)

end Geometry
