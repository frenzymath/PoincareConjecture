import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.PLAnnularStripCoordinates
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Products.SegmentStripProduct

/-!
# A finite PL rectangle-to-annular-strip homeomorphism

The actual positive-part formula maps each full longitudinal
interval bijectively onto its mitered interval. Its finite PL
image therefore supplies both directions of the strip chart.
This is a band in Hatcher's punctured-torus picture, p. 7,
for Hamilton 1976, p. 66. See M76 derivation 270.
-/

set_option autoImplicit false

open Set Geometry

namespace PLAnnularStrip

/-- The source rectangle of a finite annular strip. See
Hatcher p. 7 and M76 derivation 270. -/
def rectangle (L d : ℝ) : Set (ℝ × ℝ) := Icc 0 L ×ˢ Icc (-d) d

/-- The exact mitered strip, including its four boundary
edges. See Hatcher p. 7 and M76 derivation 270. -/
def trapezoid (L d : ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 ∈ Icc (-d) d ∧ p.1 ∈ Icc p.2 (L - p.2)}

/-- The actual strip formula is injective on its entire
rectangle, including both miter edges. See M76 derivation 270. -/
theorem stripMap_injOn {L d : ℝ} (hwidth : 4 * d < L) :
    InjOn (stripMap L) (rectangle L d) := by
  intro p hp q hq hpq
  have ht : 4 * |p.2| < L :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr hp.2) (by norm_num)) hwidth
  have h₂ : p.2 = q.2 := by
    simpa only [stripMap] using congrArg (fun z : ℝ × ℝ => z.2) hpq
  have h₁ : coordinate L p.1 p.2 = coordinate L q.1 q.2 := congrArg Prod.fst hpq
  rw [← h₂] at h₁
  exact Prod.ext ((strictMonoOn_coordinate ht).injOn hp.1 hq.1 h₁) h₂

/-- The whole image is the literal trapezoid, with no
surjectivity assumption. See M76 derivation 270. -/
theorem stripMap_image {L d : ℝ} (hwidth : 4 * d < L) :
    stripMap L '' rectangle L d = trapezoid L d := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    have ht : 4 * |q.2| < L :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr hq.2) (by norm_num)) hwidth
    refine ⟨hq.2, ?_⟩
    change coordinate L q.1 q.2 ∈ Icc q.2 (L - q.2)
    rw [← coordinate_image_Icc ht]
    exact mem_image_of_mem _ hq.1
  · rintro ⟨ht, hx⟩
    have hlt : 4 * |p.2| < L :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr ht) (by norm_num)) hwidth
    rw [← coordinate_image_Icc hlt] at hx
    obtain ⟨s, hs, he⟩ := hx
    exact ⟨(s, p.2), ⟨hs, ht⟩, Prod.ext he rfl⟩

/-- The actual positive-part strip formula gives a finite PL
homeomorphism from its rectangle onto its exact trapezoid.
In particular its end restrictions and central identity are
the previously proved coordinate formulas. See Hatcher p. 7,
Hudson pp. 15--19 and M76 derivation 270. -/
theorem exists_finitePL_strip_homeomorph {L d : ℝ}
    (hd : 0 < d) (hwidth : 4 * d < L) :
    ∃ e : rectangle L d ≃ₜ trapezoid L d,
      e.IsFinitePL ∧ ∀ p : rectangle L d, (e p : ℝ × ℝ) = stripMap L p := by
  have hL : 0 < L := by linarith
  have hex := PLStrip.exists_segmentProduct_homeomorph
    (show (0 : ℝ) ≠ L by linarith) (show -d < d by linarith)
  rw [segment_eq_Icc hL.le] at hex
  obtain ⟨e₀, he₀, _⟩ := hex
  obtain ⟨_, ⟨K, hK, hKS, _⟩, _⟩ := he₀.symm
  have hPL : FinitePiecewiseAffineOn (stripMap L) (rectangle L d) := by
    change FinitePiecewiseAffineOn (stripMap L) (Icc 0 L ×ˢ Icc (-d) d)
    rw [← hKS]
    exact finitePiecewiseAffineOn_stripMap K hK L
  have himage := hPL.exists_homeomorph_image (stripMap_injOn hwidth)
  rw [stripMap_image hwidth] at himage
  exact himage

end PLAnnularStrip
