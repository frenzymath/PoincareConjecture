import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonCutArcIntervals
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Products.AlexanderBaseProductBall

/-!
# The two literal corner arcs of a rectangle

Two adjacent sides and the opposite two adjacent sides are
finite PL intervals with the same marked diagonal endpoints.
They form the exact whole rectangle rim. Unordered intervals
retain every coordinate-sign choice used for quadrant patches.
See Hudson 1969, pp. 12--19 and M76 derivation 286h.
-/

set_option autoImplicit false

open Set Geometry

namespace RectangleCornerArcs

/-- The two complete sides adjacent to the corner `(a,c)`.
Unordered coordinate intervals permit either orientation.
See M76 derivation 286h. -/
def cornerArc (a b c d : ℝ) : Set (ℝ × ℝ) :=
  ({a} ×ˢ uIcc c d) ∪ (uIcc a b ×ˢ {c})

private theorem vertical_segment (a c d : ℝ) :
    segment ℝ (a, c) (a, d) = {a} ×ˢ uIcc c d := by
  let f : ℝ →ᵃ[ℝ] ℝ × ℝ := (AffineMap.const ℝ ℝ a).prod (AffineMap.id ℝ ℝ)
  have h := image_segment ℝ f c d
  change f '' segment ℝ c d = segment ℝ (a, c) (a, d) at h
  rw [← h, segment_eq_uIcc]
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨rfl, hx⟩
  · rintro ⟨hx, hy⟩
    exact ⟨p.2, hy, Prod.ext hx.symm rfl⟩

private theorem horizontal_segment (a b c : ℝ) :
    segment ℝ (a, c) (b, c) = uIcc a b ×ˢ {c} := by
  let f : ℝ →ᵃ[ℝ] ℝ × ℝ := (AffineMap.id ℝ ℝ).prod (AffineMap.const ℝ ℝ c)
  have h := image_segment ℝ f a b
  change f '' segment ℝ a b = segment ℝ (a, c) (b, c) at h
  rw [← h, segment_eq_uIcc]
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, rfl⟩
  · rintro ⟨hx, hy⟩
    exact ⟨p.1, hx, Prod.ext rfl hy.symm⟩

private theorem interval_pair {a b : ℝ} (hab : a ≠ b) :
    IsFinitePLBallPair ℝ (uIcc a b) {a, b} := by
  rcases lt_or_gt_of_ne hab with h | h
  · rw [uIcc_of_le h.le]
    exact isFinitePLBallPair_Icc h
  · rw [uIcc_of_ge h.le, pair_comm]
    exact isFinitePLBallPair_Icc h

/-- Each two-side corner arc is an actual finite PL interval
with its two literal opposite-side endpoints. Both coordinate
intervals must be nondegenerate. See M76 derivation 286h. -/
theorem cornerArc_ballPair {a b c d : ℝ} (hab : a ≠ b) (hcd : c ≠ d) :
    IsFinitePLBallPair ℝ (cornerArc a b c d) {(a, d), (b, c)} := by
  have hfirst : (a, d) ≠ (a, c) := fun h => hcd (congrArg Prod.snd h).symm
  have hsecond : (a, c) ≠ (b, c) := fun h => hab (congrArg Prod.fst h)
  have hinter : segment ℝ (a, d) (a, c) ∩ segment ℝ (a, c) (b, c) = {(a, c)} := by
    rw [vertical_segment, horizontal_segment, uIcc_comm d c]
    ext p
    constructor
    · rintro ⟨hp, hq⟩
      exact Prod.ext hp.1 hq.2
    · rintro rfl
      exact ⟨⟨rfl, left_mem_uIcc⟩, left_mem_uIcc, rfl⟩
  have h := isFinitePLBallPair_two_segments hfirst hsecond hinter
  rw [vertical_segment, horizontal_segment, uIcc_comm d c] at h
  exact h

/-- The corner arc lies in the complete original rectangle.
See M76 derivation 286h. -/
theorem cornerArc_subset_rectangle (a b c d : ℝ) :
    cornerArc a b c d ⊆ uIcc a b ×ˢ uIcc c d := by
  rintro p (⟨hx, hy⟩ | ⟨hx, hy⟩)
  · refine ⟨?_, hy⟩
    rw [hx]
    exact left_mem_uIcc
  · refine ⟨hx, ?_⟩
    rw [hy]
    exact left_mem_uIcc

/-- Opposite corner arcs cover exactly the four original
rectangle sides. See M76 derivation 286h. -/
theorem cornerArc_union_opposite (a b c d : ℝ) :
    cornerArc a b c d ∪ cornerArc b a d c =
      ({a, b} ×ˢ uIcc c d) ∪ (uIcc a b ×ˢ {c, d}) := by
  ext p
  simp only [cornerArc, uIcc_comm b a, uIcc_comm d c, mem_union, mem_prod,
    mem_insert_iff, mem_singleton_iff]
  tauto

/-- The two opposite corner arcs meet exactly at their two
marked endpoints. See M76 derivation 286h. -/
theorem cornerArc_inter_opposite {a b c d : ℝ} (hab : a ≠ b) (hcd : c ≠ d) :
    cornerArc a b c d ∩ cornerArc b a d c = {(a, d), (b, c)} := by
  ext p
  constructor
  · rintro ⟨(hx | hx), (hy | hy)⟩
    · exact (hab (hx.1.symm.trans hy.1)).elim
    · exact Or.inl (Prod.ext hx.1 hy.2)
    · exact Or.inr (Prod.ext hy.1 hx.2)
    · exact (hcd (hx.2.symm.trans hy.2)).elim
  · rintro (rfl | rfl)
    · exact ⟨Or.inl ⟨rfl, right_mem_uIcc⟩, Or.inr ⟨right_mem_uIcc, rfl⟩⟩
    · exact ⟨Or.inr ⟨right_mem_uIcc, rfl⟩, Or.inl ⟨rfl, right_mem_uIcc⟩⟩

/-- The rectangle is a finite PL disk whose full rim is
the union of the two literal corner arcs. See derivation 286h. -/
theorem rectangle_ballPair {a b c d : ℝ} (hab : a ≠ b) (hcd : c ≠ d) :
    IsFinitePLBallPair (ℝ × ℝ) (uIcc a b ×ˢ uIcc c d)
      (cornerArc a b c d ∪ cornerArc b a d c) := by
  rw [cornerArc_union_opposite]
  exact (interval_pair hab).prod (interval_pair hcd)

/-- Away from its two marked endpoints, the opposite arc
misses both lines through the original corner. At quadrant
patches these are exactly the height and transverse axes.
See M76 derivation 286h. -/
theorem oppositeArc_sdiff_endpoints_subset_off_axes
    {a b c d : ℝ} (hab : a ≠ b) (hcd : c ≠ d) :
    cornerArc b a d c \ {(a, d), (b, c)} ⊆ {p | p.1 ≠ a ∧ p.2 ≠ c} := by
  intro p hp
  have hrect : p ∈ uIcc a b ×ˢ uIcc c d := by
    simpa only [uIcc_comm b a, uIcc_comm d c] using
      cornerArc_subset_rectangle b a d c hp.1
  constructor
  · intro hpa
    exact hp.2 ((cornerArc_inter_opposite hab hcd).subset
      ⟨Or.inl ⟨hpa, hrect.2⟩, hp.1⟩)
  · intro hpc
    exact hp.2 ((cornerArc_inter_opposite hab hcd).subset
      ⟨Or.inr ⟨hrect.1, hpc⟩, hp.1⟩)

end RectangleCornerArcs
