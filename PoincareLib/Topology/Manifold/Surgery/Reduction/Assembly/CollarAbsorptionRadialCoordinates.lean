import PoincareLib.Topology.Manifold.Surgery.Reduction.Assembly.CollarAbsorptionBallChart
import PoincareLib.Topology.Manifold.Surgery.Reduction.Algebra.SphereNormalize
import Mathlib.Geometry.Euclidean.Inversion.Basic

/-!
# Smooth radial coordinates joining the two canonical standard ends

The signed collar coordinate of Morgan--Tian Corollary 15.4(2),
pp. 358-359, has radius `2 * (sqrt (1 + s^2) + s)`. This gives a genuine
smooth cylinder chart on punctured Euclidean space and exactly matches
the ball-compressed negative end and inverted positive end.
-/

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace PoincareMT.M74

local notation "ICollar" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

/-- The radial coordinate crossing the central sphere at radius two
(MT Corollary 15.4(2), pp. 358-359). -/
noncomputable def collarRadius (s : ℝ) : ℝ := 2 * (Real.sqrt (1 + s ^ 2) + s)

/-- The corresponding height coordinate at positive Euclidean radius
(MT Corollary 15.4(2), pp. 358-359). -/
noncomputable def collarHeight (r : ℝ) : ℝ := r / 4 - r⁻¹

/-- Every collar height has strictly positive radius
(MT Corollary 15.4(2), pp. 358-359). -/
theorem collarRadius_pos (s : ℝ) : 0 < collarRadius s := by
  have hs : |s| < Real.sqrt (1 + s ^ 2) := by
    apply (Real.lt_sqrt (abs_nonneg s)).mpr
    rw [sq_abs]
    linarith
  have h := lt_of_le_of_lt (neg_le_abs s) hs
  unfold collarRadius
  linarith

/-- Opposite heights have reciprocal radius relative to radius two
(MT Corollary 15.4(2), pp. 358-359). -/
theorem collarRadius_mul_neg (s : ℝ) : collarRadius s * collarRadius (-s) = 4 := by
  simp only [collarRadius, neg_sq]
  nlinarith [Real.sq_sqrt (show 0 ≤ 1 + s ^ 2 by positivity)]

/-- The central height has radius exactly two
(MT Corollary 15.4(2), pp. 358-359). -/
@[simp] theorem collarRadius_zero : collarRadius 0 = 2 := by norm_num [collarRadius]

/-- Radius two has height zero
(MT Corollary 15.4(2), pp. 358-359). -/
@[simp] theorem collarHeight_two : collarHeight 2 = 0 := by norm_num [collarHeight]

/-- Height recovers every signed collar parameter
(MT Corollary 15.4(2), pp. 358-359). -/
@[simp] theorem collarHeight_radius (s : ℝ) : collarHeight (collarRadius s) = s := by
  have hn : collarRadius s ≠ 0 := (collarRadius_pos s).ne'
  have hi : (collarRadius s)⁻¹ = collarRadius (-s) / 4 := by
    field_simp
    exact (collarRadius_mul_neg s).symm
  rw [collarHeight, hi]
  simp only [collarRadius, neg_sq]
  ring

private theorem collarHeight_strictMonoOn : StrictMonoOn collarHeight (Ioi (0 : ℝ)) := by
  intro a ha b hb hab
  have hi : b⁻¹ < a⁻¹ := (inv_lt_inv₀ hb ha).mpr hab
  unfold collarHeight
  linarith

/-- The positive radius is recovered from its height
(MT Corollary 15.4(2), pp. 358-359). -/
@[simp] theorem collarRadius_height {r : ℝ} (hr : 0 < r) :
    collarRadius (collarHeight r) = r := by
  apply collarHeight_strictMonoOn.injOn (collarRadius_pos _) hr
  rw [collarHeight_radius]

/-- Collar radius increases strictly with the signed parameter
(MT Corollary 15.4(2), pp. 358-359). -/
theorem collarRadius_strictMono : StrictMono collarRadius := by
  intro s t hst
  by_contra h
  have hh := collarHeight_strictMonoOn.monotoneOn
    (collarRadius_pos t) (collarRadius_pos s) (le_of_not_gt h)
  rw [collarHeight_radius, collarHeight_radius] at hh
  exact (not_le.mpr hst) hh

/-- Negative collar parameters are exactly the radii inside the central
sphere (MT Corollary 15.4(2), pp. 358-359). -/
theorem collarRadius_lt_two_iff (s : ℝ) : collarRadius s < 2 ↔ s < 0 := by
  rw [← collarRadius_zero]
  exact collarRadius_strictMono.lt_iff_lt

/-- Positive collar parameters are exactly the outer radii
(MT Corollary 15.4(2), pp. 358-359). -/
theorem collarRadius_two_lt_iff (s : ℝ) : 2 < collarRadius s ↔ 0 < s := by
  rw [← collarRadius_zero]
  exact collarRadius_strictMono.lt_iff_lt

/-- The radius is smooth through height zero
(MT Corollary 15.4(2), pp. 358-359). -/
theorem contDiff_collarRadius : ContDiff ℝ ∞ collarRadius := by
  have hs : ContDiff ℝ ∞ (fun s : ℝ => Real.sqrt (1 + s ^ 2)) :=
    (contDiff_const.add (contDiff_id.pow 2)).sqrt (by intro s; positivity)
  exact contDiff_const.mul (hs.add contDiff_id)

/-- The inverse height is smooth away from zero radius
(MT Corollary 15.4(2), pp. 358-359). -/
theorem contDiffAt_collarHeight {r : ℝ} (hr : r ≠ 0) :
    ContDiffAt ℝ ∞ collarHeight r :=
  (contDiffAt_id.div_const 4).sub (contDiffAt_id.inv hr)

/-- The radial cylinder map for the central connected-sum collar
(MT Corollary 15.4(2), pp. 358-359). -/
noncomputable def collarRadialMap (p : RoundCylinderSpace) : StandardCapSpace :=
  collarRadius p.2 • p.1.1

/-- The total inverse formula, whose asserted domain excludes zero
(MT Corollary 15.4(2), pp. 358-359). -/
noncomputable def collarRadialInverse (q0 : UnitTwoSphere) (z : StandardCapSpace) :
    RoundCylinderSpace := (sphereNormalize q0 z, collarHeight ‖z‖)

/-- The radial map's norm is exactly the specified collar radius
(MT Corollary 15.4(2), pp. 358-359). -/
theorem collarRadialMap_norm (p : RoundCylinderSpace) :
    ‖collarRadialMap p‖ = collarRadius p.2 := by
  rw [collarRadialMap, norm_smul, Real.norm_eq_abs, abs_of_pos (collarRadius_pos p.2),
    mem_sphere_zero_iff_norm.mp p.1.2, mul_one]

/-- The cylinder map never hits the Euclidean origin
(MT Corollary 15.4(2), pp. 358-359). -/
theorem collarRadialMap_ne_zero (p : RoundCylinderSpace) : collarRadialMap p ≠ 0 := by
  apply norm_pos_iff.mp
  rw [collarRadialMap_norm]
  exact collarRadius_pos p.2

/-- The inverse polar coordinates recover every cylinder point
(MT Corollary 15.4(2), pp. 358-359). -/
theorem collarRadialInverse_map (q0 : UnitTwoSphere) (p : RoundCylinderSpace) :
    collarRadialInverse q0 (collarRadialMap p) = p := by
  change (sphereNormalize q0 (collarRadius p.2 • p.1.1),
    collarHeight ‖collarRadialMap p‖) = p
  rw [sphereNormalize_pos_smul q0 p.1 (collarRadius_pos p.2),
    collarRadialMap_norm, collarHeight_radius]

/-- Every nonzero vector is recovered by the radial cylinder map
(MT Corollary 15.4(2), pp. 358-359). -/
theorem collarRadialMap_inverse (q0 : UnitTwoSphere) {z : StandardCapSpace} (hz : z ≠ 0) :
    collarRadialMap (collarRadialInverse q0 z) = z := by
  change collarRadius (collarHeight ‖z‖) • (sphereNormalize q0 z).1 = z
  rw [collarRadius_height (norm_pos_iff.mpr hz)]
  simp only [sphereNormalize, dif_neg hz]
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]

/-- The full cylinder map is smooth in both variables
(MT Corollary 15.4(2), pp. 358-359). -/
theorem collarRadialMap_contMDiff :
    ContMDiff ICollar (𝓡 3) ∞ collarRadialMap := by
  let : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) := ⟨by simp [StandardCapSpace]⟩
  exact (contDiff_collarRadius.contMDiff.comp contMDiff_snd).smul
    (contMDiff_coe_sphere.comp contMDiff_fst)

/-- The inverse cylinder coordinates are smooth on punctured Euclidean
space (MT Corollary 15.4(2), pp. 358-359). -/
theorem collarRadialInverse_contMDiffOn (q0 : UnitTwoSphere) :
    ContMDiffOn (𝓡 3) ICollar ∞ (collarRadialInverse q0) {0}ᶜ := by
  intro z hz
  apply ContMDiffAt.contMDiffWithinAt
  exact (sphereNormalize_contMDiffAt q0 hz).prodMk
    ((contDiffAt_collarHeight (norm_ne_zero_iff.mpr hz)).contMDiffAt.comp z
      (contDiffAt_norm ℝ hz).contMDiffAt)

/-- The genuine smooth cylinder chart on all nonzero Euclidean vectors
(MT Corollary 15.4(2), pp. 358-359). -/
noncomputable def collarRadialChart (q0 : UnitTwoSphere) :
    OpenPartialHomeomorph RoundCylinderSpace StandardCapSpace where
  toFun := collarRadialMap
  invFun := collarRadialInverse q0
  source := univ
  target := {0}ᶜ
  map_source' p _ := collarRadialMap_ne_zero p
  map_target' _ _ := mem_univ _
  left_inv' p _ := collarRadialInverse_map q0 p
  right_inv' _ hz := collarRadialMap_inverse q0 hz
  open_source := isOpen_univ
  open_target := isOpen_compl_singleton
  continuousOn_toFun := collarRadialMap_contMDiff.continuous.continuousOn
  continuousOn_invFun := (collarRadialInverse_contMDiffOn q0).continuousOn

/-- The cylinder chart uses every sphere point and real height
(MT Corollary 15.4(2), pp. 358-359). -/
@[simp] theorem collarRadialChart_source (q0 : UnitTwoSphere) :
    (collarRadialChart q0).source = univ := rfl

/-- Its exact target excludes just the origin
(MT Corollary 15.4(2), pp. 358-359). -/
@[simp] theorem collarRadialChart_target (q0 : UnitTwoSphere) :
    (collarRadialChart q0).target = {0}ᶜ := rfl

/-- The chart's forward map does not depend on the inverse default
(MT Corollary 15.4(2), pp. 358-359). -/
@[simp] theorem collarRadialChart_apply (q0 : UnitTwoSphere) (p : RoundCylinderSpace) :
    collarRadialChart q0 p = collarRadialMap p := rfl

/-- The chart retains the exact inverse height and direction formula
(MT Corollary 15.4(2), pp. 358-359). -/
@[simp] theorem collarRadialChart_symm_apply (q0 : UnitTwoSphere) (z : StandardCapSpace) :
    (collarRadialChart q0).symm z = collarRadialInverse q0 z := rfl

private theorem collarBallMap_inv_smul (q : UnitTwoSphere) {s : ℝ} (hs : 0 < s) :
    collarBallMap (s⁻¹ • q.1) = (2 / (Real.sqrt (1 + s ^ 2) + s)) • q.1 := by
  have hn : ‖s⁻¹ • q.1‖ = s⁻¹ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs),
      mem_sphere_zero_iff_norm.mp q.2, mul_one]
  have hr : Real.sqrt (1 + (s⁻¹) ^ 2) = Real.sqrt (1 + s ^ 2) / s := by
    rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity), div_pow,
      Real.sq_sqrt (by positivity)]
    field_simp
    ring
  rw [collarBallMap, hn, hr, smul_smul]
  congr 1
  field_simp

/-- The compressed negative canonical end has the same smooth radius
as the central collar (MT Corollary 15.4(2), pp. 358-359). -/
theorem collarBallMap_negative_end (q : UnitTwoSphere) {s : ℝ} (hs : s < 0) :
    collarBallMap ((-1 / s) • q.1) = collarRadialMap (q, s) := by
  have hi : -1 / s = (-s)⁻¹ := by simp [div_eq_mul_inv]
  rw [hi, collarBallMap_inv_smul q (neg_pos.mpr hs)]
  simp only [neg_sq]
  change (2 / (Real.sqrt (1 + s ^ 2) - s)) • q.1 =
    (2 * (Real.sqrt (1 + s ^ 2) + s)) • q.1
  congr 1
  have hd : 0 < Real.sqrt (1 + s ^ 2) - s := by
    linarith [Real.sqrt_nonneg (1 + s ^ 2)]
  apply (div_eq_iff hd.ne').mpr
  nlinarith [Real.sq_sqrt (show 0 ≤ 1 + s ^ 2 by positivity)]

/-- Radius-two inversion of the compressed positive canonical end has
that identical collar formula (MT Corollary 15.4(2), pp. 358-359). -/
theorem collarBallMap_positive_end (q : UnitTwoSphere) {s : ℝ} (hs : 0 < s) :
    EuclideanGeometry.inversion (0 : StandardCapSpace) 2
      (collarBallMap ((1 / s) • q.1)) = collarRadialMap (q, s) := by
  rw [one_div, collarBallMap_inv_smul q hs, EuclideanGeometry.inversion]
  have hd : 0 < 2 / (Real.sqrt (1 + s ^ 2) + s) := by positivity
  simp only [dist_zero_right, vsub_eq_sub, sub_zero, vadd_eq_add, add_zero,
    norm_smul, Real.norm_eq_abs, abs_of_pos hd, mem_sphere_zero_iff_norm.mp q.2, mul_one,
    smul_smul]
  change ((2 / (2 / (Real.sqrt (1 + s ^ 2) + s))) ^ 2 *
    (2 / (Real.sqrt (1 + s ^ 2) + s))) • q.1 =
      (2 * (Real.sqrt (1 + s ^ 2) + s)) • q.1
  congr 1
  field_simp

end PoincareMT.M74
