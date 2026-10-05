import PoincareLib.Topology.Manifold.Surgery.Reduction.Assembly.CollarAbsorptionAssemblyData
import Mathlib.Geometry.Euclidean.Inversion.Calculus

/-!
# The inverted cap coordinate

The second cap in the chart construction of Morgan--Tian Corollary
15.4(2), pp. 358-359, fills exactly the exterior of the radius-two
sphere. The formulas below retain their precise domains and inverses.
-/

set_option autoImplicit false

open Set Metric EuclideanGeometry
open scoped Manifold ContDiff Topology

namespace PoincareMT.M74

/-- The ball coordinate vanishes only at its original cap center
(MT Corollary 15.4(2), pp. 358-359). -/
theorem collarBallMap_eq_zero_iff (z : StandardCapSpace) : collarBallMap z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have heq := congrArg collarBallInverse h
    simpa only [collarBallInverse_map, collarBallInverse_zero] using heq
  · rintro rfl
    exact collarBallMap_zero

/-- Radius-two inversion has its usual positive radial norm formula
(MT Corollary 15.4(2), pp. 358-359). -/
theorem collarInversion_norm (z : StandardCapSpace) :
    ‖inversion (0 : StandardCapSpace) 2 z‖ = 4 / ‖z‖ := by
  simpa only [dist_zero_right, show (2 : ℝ) ^ 2 = 4 by norm_num]
    using dist_inversion_center (0 : StandardCapSpace) z (2 : ℝ)

/-- Inverting an exterior point puts it strictly inside the ball
(MT Corollary 15.4(2), pp. 358-359). -/
theorem collarInversion_mem_ball {z : StandardCapSpace} (hz : 2 < ‖z‖) :
    inversion (0 : StandardCapSpace) 2 z ∈ ball 0 2 := by
  rw [mem_ball_zero_iff, collarInversion_norm]
  apply (div_lt_iff₀ (by linarith : 0 < ‖z‖)).mpr
  linarith

/-- The outer cap coordinate is inversion of the compressed cap
(MT Corollary 15.4(2), pp. 358-359). -/
noncomputable def collarOuterMap (z : StandardCapSpace) : StandardCapSpace :=
  inversion 0 2 (collarBallMap z)

/-- Its inverse uses the ball inverse on the inverted exterior
(MT Corollary 15.4(2), pp. 358-359). -/
noncomputable def collarOuterInverse (z : StandardCapSpace) : StandardCapSpace :=
  collarBallInverse (inversion 0 2 z)

/-- The total outer formula fixes zero, outside its intended domain
(MT Corollary 15.4(2), pp. 358-359). -/
@[simp] theorem collarOuterMap_zero : collarOuterMap 0 = 0 := by
  simp [collarOuterMap]

/-- The inverse outer formula recovers its original point
(MT Corollary 15.4(2), pp. 358-359). -/
theorem collarOuterInverse_map (z : StandardCapSpace) :
    collarOuterInverse (collarOuterMap z) = z := by
  rw [collarOuterInverse, collarOuterMap, inversion_inversion 0 (by norm_num : (2 : ℝ) ≠ 0),
    collarBallInverse_map]

/-- Every exterior vector is recovered by the outer coordinate
(MT Corollary 15.4(2), pp. 358-359). -/
theorem collarOuterMap_inverse {z : StandardCapSpace} (hz : 2 < ‖z‖) :
    collarOuterMap (collarOuterInverse z) = z := by
  rw [collarOuterMap, collarOuterInverse, collarBallMap_inverse (collarInversion_mem_ball hz),
    inversion_inversion 0 (by norm_num : (2 : ℝ) ≠ 0)]

/-- The outer coordinate of a noncentral cap point lies outside radius
two (MT Corollary 15.4(2), pp. 358-359). -/
theorem collarOuterMap_norm_gt {z : StandardCapSpace} (hz : z ≠ 0) :
    2 < ‖collarOuterMap z‖ := by
  have hn : 0 < ‖collarBallMap z‖ :=
    norm_pos_iff.mpr (mt (collarBallMap_eq_zero_iff z).mp hz)
  rw [collarOuterMap, collarInversion_norm]
  apply (lt_div_iff₀ hn).mpr
  have hlt := mem_ball_zero_iff.mp (collarBallMap_mem z)
  linarith

/-- Exterior vectors have nonzero preimages in the second cap
(MT Corollary 15.4(2), pp. 358-359). -/
theorem collarOuterInverse_ne_zero {z : StandardCapSpace} (hz : 2 < ‖z‖) :
    collarOuterInverse z ≠ 0 := by
  intro h
  have heq := collarOuterMap_inverse hz
  rw [h, collarOuterMap_zero] at heq
  have : z = 0 := heq.symm
  subst z
  norm_num at hz

/-- The inverted cap formula is smooth away from its cap center
(MT Corollary 15.4(2), pp. 358-359). -/
theorem collarOuterMap_contDiffAt {z : StandardCapSpace} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ collarOuterMap z :=
  contDiffAt_const.inversion contDiffAt_const contDiff_collarBallMap.contDiffAt
    (mt (collarBallMap_eq_zero_iff z).mp hz)

/-- The outer inverse is smooth throughout the exterior region
(MT Corollary 15.4(2), pp. 358-359). -/
theorem collarOuterInverse_contDiffAt {z : StandardCapSpace} (hz : 2 < ‖z‖) :
    ContDiffAt ℝ ∞ collarOuterInverse z := by
  have hne : z ≠ 0 := norm_pos_iff.mp (by linarith)
  exact (contDiffOn_collarBallInverse.contDiffAt
    (isOpen_ball.mem_nhds (collarInversion_mem_ball hz))).comp z
      (contDiffAt_const.inversion contDiffAt_const contDiffAt_id hne)

/-- Reversing collar height is exactly radius-two inversion in the
radial chart (MT Corollary 15.4(2), pp. 358-359). -/
theorem collarRadialMap_reflect (p : RoundCylinderSpace) :
    inversion (0 : StandardCapSpace) 2 (collarRadialMap p) =
      collarRadialMap (collarReflect p) := by
  rw [inversion]
  simp only [dist_zero_right, vsub_eq_sub, sub_zero, vadd_eq_add, add_zero]
  rw [collarRadialMap_norm]
  simp only [collarRadialMap, collarReflect, smul_smul]
  congr 1
  have hn := (collarRadius_pos p.2).ne'
  have heq := collarRadius_mul_neg p.2
  field_simp
  nlinarith

end PoincareMT.M74
