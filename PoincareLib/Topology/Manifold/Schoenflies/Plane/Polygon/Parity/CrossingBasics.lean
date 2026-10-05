import PoincareLib.Topology.Manifold.Schoenflies.Plane.Polygon.LineLevel
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic

/-!
# Coordinate-ray crossings of segments

Auxiliaries for polygonal separation in Cairns (1951), Theorem 2.1 and
Lemma 2.1, pp. 860-861, using the alternative crossing-parity route.
The lower height endpoint is counted and the upper endpoint excluded.
For arbitrary linear maps the coordinate ray means its preimage; the
geometric ray interpretation uses an actual planar coordinate frame.
See `smale/derivations/2026-09-21-crossing-basics.md` for sources and scope.
-/

set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies.Plane

/-- A height threshold indicator modulo two; auxiliary to Cairns, 2.1, pp. 860-861. -/
noncomputable def heightStep (a y : ℝ) : ZMod 2 := by
  classical
  exact if a ≤ y then 1 else 0

/-- The lower-closed, upper-open endpoint-height test; Cairns, 2.1, pp. 860-861, auxiliary. -/
def heightCrossing (a b y : ℝ) : Prop :=
  min a b ≤ y ∧ y < max a b

/-- A counted level has distinct endpoint heights; auxiliary to Cairns, 2.1, pp. 860-861. -/
theorem heightCrossing_ne {a b y : ℝ} (h : heightCrossing a b y) : a ≠ b := by
  rintro rfl
  simp only [heightCrossing, min_self, max_self] at h
  exact not_lt_of_ge h.1 h.2

/-- The height test covers either edge orientation; auxiliary to Cairns, 2.1, pp. 860-861. -/
theorem heightCrossing_iff (a b y : ℝ) :
    heightCrossing a b y ↔ (a ≤ y ∧ y < b) ∨ (b ≤ y ∧ y < a) := by
  rcases le_total a b with hab | hba
  · rw [heightCrossing, min_eq_left hab, max_eq_right hab]
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · exact (not_lt_of_ge (hab.trans h.1) h.2).elim
  · rw [heightCrossing, min_eq_right hba, max_eq_left hba]
    constructor
    · exact Or.inr
    · rintro (h | h)
      · exact (not_lt_of_ge (hba.trans h.1) h.2).elim
      · exact h

open Classical in
/-- A height crossing is the sum of endpoint indicators modulo two;
auxiliary to Cairns, Theorem 2.1, pp. 860-861. -/
theorem heightCrossing_indicator (a b y : ℝ) :
    (if heightCrossing a b y then 1 else 0 : ZMod 2) = heightStep a y + heightStep b y := by
  rcases le_or_gt a y with ha | ha <;> rcases le_or_gt b y with hb | hb
  · simp [heightStep, heightCrossing_iff, ha, hb, not_lt_of_ge ha, not_lt_of_ge hb,
      CharTwo.add_self_eq_zero]
  · simp [heightStep, heightCrossing_iff, ha, hb, not_lt_of_ge ha, not_le_of_gt hb]
  · simp [heightStep, heightCrossing_iff, ha, hb, not_le_of_gt ha, not_lt_of_ge hb]
  · simp [heightStep, heightCrossing_iff, ha, hb, not_le_of_gt ha, not_le_of_gt hb]

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A segment meets the forward coordinate ray, with the upper vertex excluded;
auxiliary to Cairns, Theorem 2.1, pp. 860-861. -/
def segmentCrossesRay (X H : E →ₗ[ℝ] ℝ) (a b q : E) : Prop :=
  heightCrossing (H a) (H b) (H q) ∧ X q < X (lineLevelPoint H a b (H q))

/-- The contribution of one segment modulo two; auxiliary to Cairns, 2.1, pp. 860-861. -/
noncomputable def segmentRayParity (X H : E →ₗ[ℝ] ℝ) (a b q : E) : ZMod 2 := by
  classical
  exact if segmentCrossesRay X H a b q then 1 else 0

/-- Every counted intersection is an actual segment point;
auxiliary to Cairns, Theorem 2.1, pp. 860-861. -/
theorem segmentCrossesRay_point_mem_segment (X H : E →ₗ[ℝ] ℝ) {a b q : E}
    (h : segmentCrossesRay X H a b q) : lineLevelPoint H a b (H q) ∈ segment ℝ a b :=
  (lineLevelPoint_mem_segment_iff H (heightCrossing_ne h.1) (H q)).mpr ⟨h.1.1, h.1.2.le⟩

/-- The crossing test has its stated segment-intersection meaning;
auxiliary to Cairns, Theorem 2.1, pp. 860-861. -/
theorem segmentCrossesRay_iff_exists (X H : E →ₗ[ℝ] ℝ) {a b q : E} (hab : H a ≠ H b) :
    segmentCrossesRay X H a b q ↔ H q < max (H a) (H b) ∧
      ∃ x ∈ segment ℝ a b, H x = H q ∧ X q < X x := by
  constructor
  · intro h
    exact ⟨h.1.2, _, segmentCrossesRay_point_mem_segment X H h,
      linearMap_lineLevelPoint H hab (H q), h.2⟩
  · rintro ⟨hy, x, hx, hxH, hxX⟩
    have hmx : lineLevelPoint H a b (H q) = x := by
      rw [← hxH]
      exact lineLevelPoint_eq_of_mem_segment H hab hx
    have hm : lineLevelPoint H a b (H q) ∈ segment ℝ a b := by rwa [hmx]
    have hi := (lineLevelPoint_mem_segment_iff H hab (H q)).mp hm
    exact ⟨⟨hi.1, hy⟩, by simpa only [hmx] using hxX⟩

/-- A ray based beyond both endpoints cannot cross the segment;
auxiliary to Cairns, Theorem 2.1, pp. 860-861. -/
theorem not_segmentCrossesRay_of_right_endpoints (X H : E →ₗ[ℝ] ℝ) {a b q : E}
    (ha : X a ≤ X q) (hb : X b ≤ X q) : ¬segmentCrossesRay X H a b q := by
  intro h
  have himage : X '' segment ℝ a b = uIcc (X a) (X b) := by
    simpa only [segment_eq_uIcc, LinearMap.coe_toAffineMap] using
      image_segment ℝ X.toAffineMap a b
  have hi := himage ▸ mem_image_of_mem X (segmentCrossesRay_point_mem_segment X H h)
  exact not_lt_of_ge (hi.2.trans (max_le ha hb)) h.2

/-- The segment parity vanishes beyond both endpoints;
auxiliary to Cairns, Theorem 2.1, pp. 860-861. -/
theorem segmentRayParity_eq_zero_of_right_endpoints (X H : E →ₗ[ℝ] ℝ) {a b q : E}
    (ha : X a ≤ X q) (hb : X b ≤ X q) : segmentRayParity X H a b q = 0 := by
  exact if_neg (not_segmentCrossesRay_of_right_endpoints X H ha hb)

/-- To the left of the line intersection only the height test remains;
auxiliary to Cairns, Theorem 2.1, pp. 860-861. -/
theorem segmentRayParity_eq_heightStep_of_left (X H : E →ₗ[ℝ] ℝ) {a b q : E}
    (hX : X q < X (lineLevelPoint H a b (H q))) :
    segmentRayParity X H a b q = heightStep (H a) (H q) + heightStep (H b) (H q) := by
  classical
  simpa only [segmentRayParity, segmentCrossesRay, hX, and_true] using
    heightCrossing_indicator (H a) (H b) (H q)

/-- At or to the right of the line intersection no crossing is counted;
auxiliary to Cairns, Theorem 2.1, pp. 860-861. -/
theorem segmentRayParity_eq_zero_of_right (X H : E →ₗ[ℝ] ℝ) {a b q : E}
    (hX : X (lineLevelPoint H a b (H q)) ≤ X q) : segmentRayParity X H a b q = 0 := by
  simp [segmentRayParity, segmentCrossesRay, not_lt_of_ge hX]

/-- Left of both endpoints the parity is the endpoint-height sum;
auxiliary to Cairns, Theorem 2.1, pp. 860-861. -/
theorem segmentRayParity_eq_heightStep_of_left_endpoints (X H : E →ₗ[ℝ] ℝ) {a b q : E}
    (ha : X q < X a) (hb : X q < X b) :
    segmentRayParity X H a b q = heightStep (H a) (H q) + heightStep (H b) (H q) := by
  classical
  by_cases hh : heightCrossing (H a) (H b) (H q)
  · have hm := (lineLevelPoint_mem_segment_iff H (heightCrossing_ne hh) (H q)).mpr
      ⟨hh.1, hh.2.le⟩
    have himage : X '' segment ℝ a b = uIcc (X a) (X b) := by
      simpa only [segment_eq_uIcc, LinearMap.coe_toAffineMap] using
        image_segment ℝ X.toAffineMap a b
    have hi := himage ▸ mem_image_of_mem X hm
    exact segmentRayParity_eq_heightStep_of_left X H ((lt_min ha hb).trans_le hi.1)
  · rw [← heightCrossing_indicator]
    simp [segmentRayParity, segmentCrossesRay, hh]

/-- At the initial vertex's height, precisely an ascending edge is counted;
auxiliary to Cairns, Theorem 2.1, pp. 860-861. -/
theorem segmentCrossesRay_left_height (X H : E →ₗ[ℝ] ℝ) {a b q : E} (hq : H q = H a) :
    segmentCrossesRay X H a b q ↔ H a < H b ∧ X q < X a := by
  simp [segmentCrossesRay, hq, heightCrossing_iff, lineLevelPoint_left]

/-- At the terminal vertex's height, precisely a descending edge is counted;
auxiliary to Cairns, Theorem 2.1, pp. 860-861. -/
theorem segmentCrossesRay_right_height (X H : E →ₗ[ℝ] ℝ) {a b q : E} (hq : H q = H b) :
    segmentCrossesRay X H a b q ↔ H b < H a ∧ X q < X b := by
  by_cases hab : H a = H b
  · simp [segmentCrossesRay, hq, hab, heightCrossing]
  · simp [segmentCrossesRay, hq, heightCrossing_iff, lineLevelPoint_right H hab]

end Poincare.Manifold.Schoenflies.Plane
