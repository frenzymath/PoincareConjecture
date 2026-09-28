import PoincareConjecture.Proofs.M74.Cor15_4.CollarAbsorptionBallChart
import PoincareConjecture.Proofs.M74.Mathlib.SphereNormalize
import Mathlib.Geometry.Euclidean.Inversion.Basic










set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace PoincareConjecture.M74

local notation "ICollar" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)



noncomputable def collarRadius (s : ℝ) : ℝ := 2 * (Real.sqrt (1 + s ^ 2) + s)



noncomputable def collarHeight (r : ℝ) : ℝ := r / 4 - r⁻¹



theorem collarRadius_pos (s : ℝ) : 0 < collarRadius s := by
  have hs : |s| < Real.sqrt (1 + s ^ 2) := by
    apply (Real.lt_sqrt (abs_nonneg s)).mpr
    rw [sq_abs]
    linarith
  have h := lt_of_le_of_lt (neg_le_abs s) hs
  unfold collarRadius
  linarith



theorem collarRadius_mul_neg (s : ℝ) : collarRadius s * collarRadius (-s) = 4 := by
  simp only [collarRadius, neg_sq]
  nlinarith [Real.sq_sqrt (show 0 ≤ 1 + s ^ 2 by positivity)]



@[simp] theorem collarRadius_zero : collarRadius 0 = 2 := by norm_num [collarRadius]



@[simp] theorem collarHeight_two : collarHeight 2 = 0 := by norm_num [collarHeight]



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



@[simp] theorem collarRadius_height {r : ℝ} (hr : 0 < r) :
    collarRadius (collarHeight r) = r := by
  apply collarHeight_strictMonoOn.injOn (collarRadius_pos _) hr
  rw [collarHeight_radius]



theorem collarRadius_strictMono : StrictMono collarRadius := by
  intro s t hst
  by_contra h
  have hh := collarHeight_strictMonoOn.monotoneOn
    (collarRadius_pos t) (collarRadius_pos s) (le_of_not_gt h)
  rw [collarHeight_radius, collarHeight_radius] at hh
  exact (not_le.mpr hst) hh



theorem collarRadius_lt_two_iff (s : ℝ) : collarRadius s < 2 ↔ s < 0 := by
  rw [← collarRadius_zero]
  exact collarRadius_strictMono.lt_iff_lt



theorem collarRadius_two_lt_iff (s : ℝ) : 2 < collarRadius s ↔ 0 < s := by
  rw [← collarRadius_zero]
  exact collarRadius_strictMono.lt_iff_lt



theorem contDiff_collarRadius : ContDiff ℝ ∞ collarRadius := by
  have hs : ContDiff ℝ ∞ (fun s : ℝ => Real.sqrt (1 + s ^ 2)) :=
    (contDiff_const.add (contDiff_id.pow 2)).sqrt (by intro s; positivity)
  exact contDiff_const.mul (hs.add contDiff_id)



theorem contDiffAt_collarHeight {r : ℝ} (hr : r ≠ 0) :
    ContDiffAt ℝ ∞ collarHeight r :=
  (contDiffAt_id.div_const 4).sub (contDiffAt_id.inv hr)



noncomputable def collarRadialMap (p : RoundCylinderSpace) : StandardCapSpace :=
  collarRadius p.2 • p.1.1



noncomputable def collarRadialInverse (q0 : UnitTwoSphere) (z : StandardCapSpace) :
    RoundCylinderSpace := (sphereNormalize q0 z, collarHeight ‖z‖)



theorem collarRadialMap_norm (p : RoundCylinderSpace) :
    ‖collarRadialMap p‖ = collarRadius p.2 := by
  rw [collarRadialMap, norm_smul, Real.norm_eq_abs, abs_of_pos (collarRadius_pos p.2),
    mem_sphere_zero_iff_norm.mp p.1.2, mul_one]



theorem collarRadialMap_ne_zero (p : RoundCylinderSpace) : collarRadialMap p ≠ 0 := by
  apply norm_pos_iff.mp
  rw [collarRadialMap_norm]
  exact collarRadius_pos p.2



theorem collarRadialInverse_map (q0 : UnitTwoSphere) (p : RoundCylinderSpace) :
    collarRadialInverse q0 (collarRadialMap p) = p := by
  change (sphereNormalize q0 (collarRadius p.2 • p.1.1),
    collarHeight ‖collarRadialMap p‖) = p
  rw [sphereNormalize_pos_smul q0 p.1 (collarRadius_pos p.2),
    collarRadialMap_norm, collarHeight_radius]



theorem collarRadialMap_inverse (q0 : UnitTwoSphere) {z : StandardCapSpace} (hz : z ≠ 0) :
    collarRadialMap (collarRadialInverse q0 z) = z := by
  change collarRadius (collarHeight ‖z‖) • (sphereNormalize q0 z).1 = z
  rw [collarRadius_height (norm_pos_iff.mpr hz)]
  simp only [sphereNormalize, dif_neg hz]
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]



theorem collarRadialMap_contMDiff :
    ContMDiff ICollar (𝓡 3) ∞ collarRadialMap := by
  let : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) := ⟨by simp [StandardCapSpace]⟩
  exact (contDiff_collarRadius.contMDiff.comp contMDiff_snd).smul
    (contMDiff_coe_sphere.comp contMDiff_fst)



theorem collarRadialInverse_contMDiffOn (q0 : UnitTwoSphere) :
    ContMDiffOn (𝓡 3) ICollar ∞ (collarRadialInverse q0) {0}ᶜ := by
  intro z hz
  apply ContMDiffAt.contMDiffWithinAt
  exact (sphereNormalize_contMDiffAt q0 hz).prodMk
    ((contDiffAt_collarHeight (norm_ne_zero_iff.mpr hz)).contMDiffAt.comp z
      (contDiffAt_norm ℝ hz).contMDiffAt)



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



@[simp] theorem collarRadialChart_source (q0 : UnitTwoSphere) :
    (collarRadialChart q0).source = univ := rfl



@[simp] theorem collarRadialChart_target (q0 : UnitTwoSphere) :
    (collarRadialChart q0).target = {0}ᶜ := rfl



@[simp] theorem collarRadialChart_apply (q0 : UnitTwoSphere) (p : RoundCylinderSpace) :
    collarRadialChart q0 p = collarRadialMap p := rfl



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

end PoincareConjecture.M74
