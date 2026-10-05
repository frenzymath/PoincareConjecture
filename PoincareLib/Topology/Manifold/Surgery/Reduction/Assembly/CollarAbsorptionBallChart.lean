import PoincareLib.Topology.Manifold.ConnectedSum.SphereReduction
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# A radial ball chart adapted to the canonical connected-sum ends

For Morgan--Tian Corollary 15.4(2), pp. 358-359, the radial chart below
has an exact smooth transition across ends parametrized by `1 / s`.
Its target is the actual radius-two Euclidean ball, and its inverse is
proved on that full target.
-/

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace PoincareMT.M74

/-- Radial compression adapted to the canonical end height
(MT Corollary 15.4(2), pp. 358-359). -/
noncomputable def collarBallMap (x : StandardCapSpace) : StandardCapSpace :=
  (2 / (Real.sqrt (1 + ‖x‖ ^ 2) + 1)) • x

/-- The exact inverse radial formula on the radius-two ball
(MT Corollary 15.4(2), pp. 358-359). -/
noncomputable def collarBallInverse (y : StandardCapSpace) : StandardCapSpace :=
  (4 / (4 - ‖y‖ ^ 2)) • y

/-- The radial compression is smooth even at the origin because its
coefficient depends on squared norm (MT Corollary 15.4(2), pp. 358-359). -/
theorem contDiff_collarBallMap : ContDiff ℝ ∞ collarBallMap := by
  have hs : ContDiff ℝ ∞ (fun x : StandardCapSpace => Real.sqrt (1 + ‖x‖ ^ 2)) :=
    (contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (by intro x; positivity)
  exact (contDiff_const.div (hs.add contDiff_const) (by intro x; positivity)).smul contDiff_id

/-- The inverse radial formula is smooth on its exact ball domain
(MT Corollary 15.4(2), pp. 358-359). -/
theorem contDiffOn_collarBallInverse :
    ContDiffOn ℝ ∞ collarBallInverse (ball (0 : StandardCapSpace) 2) := by
  intro y hy
  have hd : 0 < 4 - ‖y‖ ^ 2 := by
    nlinarith [norm_nonneg y, mem_ball_zero_iff.mp hy]
  exact ((contDiffAt_const.div
    (contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt) hd.ne').smul
      contDiffAt_id).contDiffWithinAt

/-- The compression's norm is its positive radial scalar
(MT Corollary 15.4(2), pp. 358-359). -/
theorem collarBallMap_norm (x : StandardCapSpace) :
    ‖collarBallMap x‖ = (2 / (Real.sqrt (1 + ‖x‖ ^ 2) + 1)) * ‖x‖ := by
  rw [collarBallMap, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- Every compressed point is strictly inside the radius-two ball
(MT Corollary 15.4(2), pp. 358-359). -/
theorem collarBallMap_mem (x : StandardCapSpace) :
    collarBallMap x ∈ ball (0 : StandardCapSpace) 2 := by
  rw [mem_ball_zero_iff, collarBallMap_norm]
  have hlt : ‖x‖ < Real.sqrt (1 + ‖x‖ ^ 2) :=
    (Real.lt_sqrt (norm_nonneg x)).mpr (by linarith)
  have hd : 0 < Real.sqrt (1 + ‖x‖ ^ 2) + 1 := by positivity
  rw [div_mul_eq_mul_div, div_lt_iff₀ hd]
  linarith

/-- The ball map fixes the Euclidean origin
(MT Corollary 15.4(2), pp. 358-359). -/
@[simp] theorem collarBallMap_zero : collarBallMap 0 = 0 := by simp [collarBallMap]

/-- The inverse radial formula also fixes the origin
(MT Corollary 15.4(2), pp. 358-359). -/
@[simp] theorem collarBallInverse_zero : collarBallInverse 0 = 0 := by
  simp [collarBallInverse]

private theorem collarBallMap_denominator (x : StandardCapSpace) :
    4 - ‖collarBallMap x‖ ^ 2 = 8 / (Real.sqrt (1 + ‖x‖ ^ 2) + 1) := by
  rw [collarBallMap_norm]
  have hd : Real.sqrt (1 + ‖x‖ ^ 2) + 1 ≠ 0 := by positivity
  have hs := Real.sq_sqrt (show 0 ≤ 1 + ‖x‖ ^ 2 by positivity)
  field_simp
  nlinarith

/-- The radial inverse recovers every original Euclidean point
(MT Corollary 15.4(2), pp. 358-359). -/
theorem collarBallInverse_map (x : StandardCapSpace) :
    collarBallInverse (collarBallMap x) = x := by
  rw [collarBallInverse, collarBallMap_denominator, collarBallMap, smul_smul]
  have hd : Real.sqrt (1 + ‖x‖ ^ 2) + 1 ≠ 0 := by positivity
  have hc : 4 / (8 / (Real.sqrt (1 + ‖x‖ ^ 2) + 1)) *
      (2 / (Real.sqrt (1 + ‖x‖ ^ 2) + 1)) = 1 := by
    field_simp
    norm_num
  rw [hc, one_smul]

/-- Every point of the full radius-two ball is recovered by compression
(MT Corollary 15.4(2), pp. 358-359). -/
theorem collarBallMap_inverse {y : StandardCapSpace} (hy : y ∈ ball (0 : StandardCapSpace) 2) :
    collarBallMap (collarBallInverse y) = y := by
  have hd : 0 < 4 - ‖y‖ ^ 2 := by
    nlinarith [norm_nonneg y, mem_ball_zero_iff.mp hy]
  have hn : ‖collarBallInverse y‖ = (4 / (4 - ‖y‖ ^ 2)) * ‖y‖ := by
    rw [collarBallInverse, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hs : Real.sqrt (1 + ‖collarBallInverse y‖ ^ 2) =
      (4 + ‖y‖ ^ 2) / (4 - ‖y‖ ^ 2) := by
    rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity), hn]
    field_simp
    ring
  rw [collarBallMap, hs, collarBallInverse, smul_smul]
  have hc : 2 / ((4 + ‖y‖ ^ 2) / (4 - ‖y‖ ^ 2) + 1) *
      (4 / (4 - ‖y‖ ^ 2)) = 1 := by field_simp; ring
  rw [hc, one_smul]

/-- The genuine radial open partial homeomorphism used to compactify
each Euclidean end (MT Corollary 15.4(2), pp. 358-359). -/
noncomputable def collarBallChart :
    OpenPartialHomeomorph StandardCapSpace StandardCapSpace where
  toFun := collarBallMap
  invFun := collarBallInverse
  source := univ
  target := ball 0 2
  map_source' x _ := collarBallMap_mem x
  map_target' _ _ := mem_univ _
  left_inv' x _ := collarBallInverse_map x
  right_inv' _ hy := collarBallMap_inverse hy
  open_source := isOpen_univ
  open_target := isOpen_ball
  continuousOn_toFun := contDiff_collarBallMap.continuous.continuousOn
  continuousOn_invFun := contDiffOn_collarBallInverse.continuousOn

/-- The ball chart has unrestricted Euclidean source
(MT Corollary 15.4(2), pp. 358-359). -/
@[simp] theorem collarBallChart_source : collarBallChart.source = univ := rfl

/-- The exact chart target is the radius-two ball
(MT Corollary 15.4(2), pp. 358-359). -/
@[simp] theorem collarBallChart_target :
    collarBallChart.target = ball (0 : StandardCapSpace) 2 := rfl

/-- The chart retains the chosen smooth radial formula
(MT Corollary 15.4(2), pp. 358-359). -/
@[simp] theorem collarBallChart_apply (x : StandardCapSpace) :
    collarBallChart x = collarBallMap x := rfl

/-- Its inverse retains the exact rational formula on the target
(MT Corollary 15.4(2), pp. 358-359). -/
@[simp] theorem collarBallChart_symm_apply (x : StandardCapSpace) :
    collarBallChart.symm x = collarBallInverse x := rfl

end PoincareMT.M74
