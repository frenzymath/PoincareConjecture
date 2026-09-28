import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.LineLevel
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic












set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies.Plane


noncomputable def heightStep (a y : ℝ) : ZMod 2 := by
  classical
  exact if a ≤ y then 1 else 0


def heightCrossing (a b y : ℝ) : Prop :=
  min a b ≤ y ∧ y < max a b


theorem heightCrossing_ne {a b y : ℝ} (h : heightCrossing a b y) : a ≠ b := by
  rintro rfl
  simp only [heightCrossing, min_self, max_self] at h
  exact not_lt_of_ge h.1 h.2


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


theorem heightCrossing_indicator (a b y : ℝ) :
    (if heightCrossing a b y then 1 else 0 : ZMod 2) = heightStep a y + heightStep b y := by
  rcases le_or_gt a y with ha | ha <;> rcases le_or_gt b y with hb | hb
  · simp [heightStep, heightCrossing_iff, ha, hb, not_lt_of_ge ha, not_lt_of_ge hb,
      CharTwo.add_self_eq_zero]
  · simp [heightStep, heightCrossing_iff, ha, hb, not_lt_of_ge ha, not_le_of_gt hb]
  · simp [heightStep, heightCrossing_iff, ha, hb, not_le_of_gt ha, not_lt_of_ge hb]
  · simp [heightStep, heightCrossing_iff, ha, hb, not_le_of_gt ha, not_le_of_gt hb]

variable {E : Type*} [AddCommGroup E] [Module ℝ E]



def segmentCrossesRay (X H : E →ₗ[ℝ] ℝ) (a b q : E) : Prop :=
  heightCrossing (H a) (H b) (H q) ∧ X q < X (lineLevelPoint H a b (H q))


noncomputable def segmentRayParity (X H : E →ₗ[ℝ] ℝ) (a b q : E) : ZMod 2 := by
  classical
  exact if segmentCrossesRay X H a b q then 1 else 0



theorem segmentCrossesRay_point_mem_segment (X H : E →ₗ[ℝ] ℝ) {a b q : E}
    (h : segmentCrossesRay X H a b q) : lineLevelPoint H a b (H q) ∈ segment ℝ a b :=
  (lineLevelPoint_mem_segment_iff H (heightCrossing_ne h.1) (H q)).mpr ⟨h.1.1, h.1.2.le⟩



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



theorem not_segmentCrossesRay_of_right_endpoints (X H : E →ₗ[ℝ] ℝ) {a b q : E}
    (ha : X a ≤ X q) (hb : X b ≤ X q) : ¬segmentCrossesRay X H a b q := by
  intro h
  have himage : X '' segment ℝ a b = uIcc (X a) (X b) := by
    simpa only [segment_eq_uIcc, LinearMap.coe_toAffineMap] using
      image_segment ℝ X.toAffineMap a b
  have hi := himage ▸ mem_image_of_mem X (segmentCrossesRay_point_mem_segment X H h)
  exact not_lt_of_ge (hi.2.trans (max_le ha hb)) h.2



theorem segmentRayParity_eq_zero_of_right_endpoints (X H : E →ₗ[ℝ] ℝ) {a b q : E}
    (ha : X a ≤ X q) (hb : X b ≤ X q) : segmentRayParity X H a b q = 0 := by
  exact if_neg (not_segmentCrossesRay_of_right_endpoints X H ha hb)



theorem segmentRayParity_eq_heightStep_of_left (X H : E →ₗ[ℝ] ℝ) {a b q : E}
    (hX : X q < X (lineLevelPoint H a b (H q))) :
    segmentRayParity X H a b q = heightStep (H a) (H q) + heightStep (H b) (H q) := by
  classical
  simpa only [segmentRayParity, segmentCrossesRay, hX, and_true] using
    heightCrossing_indicator (H a) (H b) (H q)



theorem segmentRayParity_eq_zero_of_right (X H : E →ₗ[ℝ] ℝ) {a b q : E}
    (hX : X (lineLevelPoint H a b (H q)) ≤ X q) : segmentRayParity X H a b q = 0 := by
  simp [segmentRayParity, segmentCrossesRay, not_lt_of_ge hX]



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



theorem segmentCrossesRay_left_height (X H : E →ₗ[ℝ] ℝ) {a b q : E} (hq : H q = H a) :
    segmentCrossesRay X H a b q ↔ H a < H b ∧ X q < X a := by
  simp [segmentCrossesRay, hq, heightCrossing_iff, lineLevelPoint_left]



theorem segmentCrossesRay_right_height (X H : E →ₗ[ℝ] ℝ) {a b q : E} (hq : H q = H b) :
    segmentCrossesRay X H a b q ↔ H b < H a ∧ X q < X b := by
  by_cases hab : H a = H b
  · simp [segmentCrossesRay, hq, hab, heightCrossing]
  · simp [segmentCrossesRay, hq, heightCrossing_iff, lineLevelPoint_right H hab]

end Poincare.Manifold.Schoenflies.Plane
