import Mathlib.Geometry.Polygon.Basic
import Mathlib.Topology.Algebra.Affine
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Nonvertical planar segments as height graphs

The affine line through two points with distinct first coordinates
is the graph of a continuous height function. Its segment is exactly
the portion over the unordered closed endpoint interval. This is the
coordinate calculation in Erickson, Simple Polygons, Section 1.3,
pp. 5--6; see M76 derivation 95.
-/

set_option autoImplicit false

open Set AffineMap

namespace PlanarSegment

/-- Height on the affine line through two planar points. Correctness
as a graph requires distinct first coordinates. See Erickson pp. 5--6
and M76 derivation 95. -/
noncomputable def height (a b : ℝ × ℝ) (x : ℝ) : ℝ :=
  lineMap a.2 b.2 ((x - a.1) / (b.1 - a.1))

/-- The total height formula is continuous, including when the
endpoint first coordinates coincide. See M76 derivation 95. -/
theorem continuous_height (a b : ℝ × ℝ) : Continuous (height a b) := by
  unfold height
  simp only [lineMap_apply_module', smul_eq_mul]
  fun_prop

/-- The height graph passes through its first endpoint.
See M76 derivation 95. -/
theorem height_left (a b : ℝ × ℝ) : height a b a.1 = a.2 := by
  simp [height]

/-- The height graph passes through its second endpoint when the
edge is nonvertical. See M76 derivation 95. -/
theorem height_right {a b : ℝ × ℝ} (hab : a.1 ≠ b.1) :
    height a b b.1 = b.2 := by
  simp [height, sub_ne_zero.mpr hab.symm]

private theorem horizontal_parameter {a b x : ℝ} (hab : a ≠ b) :
    lineMap a b ((x - a) / (b - a)) = x := by
  rw [lineMap_apply_module']
  simp only [smul_eq_mul]
  rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hab.symm)]
  ring

private theorem recover_parameter {a b t : ℝ} (hab : a ≠ b) :
    (lineMap a b t - a) / (b - a) = t := by
  rw [lineMap_apply_module']
  simp only [smul_eq_mul, add_sub_cancel_right]
  exact mul_div_cancel_right₀ t (sub_ne_zero.mpr hab.symm)

/-- The height graph is the original affine line parameterization
with first coordinate as parameter. See M76 derivation 95. -/
theorem graph_eq_lineMap {a b : ℝ × ℝ} (hab : a.1 ≠ b.1) (x : ℝ) :
    (x, height a b x) = lineMap a b ((x - a.1) / (b.1 - a.1)) := by
  apply Prod.ext
  · exact (horizontal_parameter hab).symm
  · exact (snd_lineMap _ _ _).symm

/-- Segment membership is precisely the height equation over the
closed horizontal endpoint interval. See Erickson pp. 5--6 and
M76 derivation 95. -/
theorem mem_segment_iff {a b q : ℝ × ℝ} (hab : a.1 ≠ b.1) :
    q ∈ segment ℝ a b ↔ q.1 ∈ uIcc a.1 b.1 ∧ q.2 = height a b q.1 := by
  constructor
  · intro hq
    rw [segment_eq_image_lineMap] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    constructor
    · rw [fst_lineMap, ← segment_eq_uIcc, segment_eq_image_lineMap]
      exact ⟨t, ht, rfl⟩
    · rw [snd_lineMap, height, fst_lineMap, recover_parameter hab]
  · rintro ⟨hq, hheight⟩
    have ht : (q.1 - a.1) / (b.1 - a.1) ∈ Icc (0 : ℝ) 1 := by
      rcases lt_or_gt_of_ne hab with hab | hba
      · rw [uIcc_of_le hab.le] at hq
        exact ⟨div_nonneg (sub_nonneg.mpr hq.1) (sub_pos.mpr hab).le,
          (div_le_one (sub_pos.mpr hab)).mpr (sub_le_sub_right hq.2 _)⟩
      · rw [uIcc_of_ge hba.le] at hq
        exact ⟨div_nonneg_of_nonpos (sub_nonpos.mpr hq.2) (sub_neg.mpr hba).le,
          (div_le_one_of_neg (sub_neg.mpr hba)).mpr (sub_le_sub_right hq.1 _)⟩
    rw [segment_eq_image_lineMap]
    refine ⟨_, ht, ?_⟩
    rw [← graph_eq_lineMap hab, ← hheight]

end PlanarSegment
