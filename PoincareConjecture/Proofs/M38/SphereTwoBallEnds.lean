import PoincareConjecture.Proofs.M38.CylinderRegionTransport
import PoincareConjecture.Proofs.M38.SphereTwoBallReduction
import PoincareConjecture.Proofs.M38.SpherePoleNormalization
import PoincareConjecture.Proofs.M38.CenteredEuclideanBall











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

private instance sphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩


theorem punctureCollapse_ray (z : UnitTwoSphere) {t : ℝ} (ht : 0 < t) :
    punctureCollapse (t • z.val) = punctureRadialOrderIso t • z.val := by
  rw [punctureCollapse, capRadialMap, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
    show ‖z.val‖ = 1 by simp, mul_one, smul_smul, div_mul_cancel₀ _ ht.ne']


noncomputable def spherePoleDirection (a : UnitThreeSphere)
    (L : StandardCapSpace ≃L[ℝ] StandardCapSpace) :
    Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞ :=
  linearSphereDiffeomorph
    (L.trans (threeSphereStereoOppositeIsometry a).toContinuousLinearEquiv)


theorem spherePoleDirection_coe (a : UnitThreeSphere)
    (L : StandardCapSpace ≃L[ℝ] StandardCapSpace) (z : UnitTwoSphere) :
    (spherePoleDirection a L z).val =
      threeSphereStereoOppositeIsometry a (linearSphereDiffeomorph L z).val := by
  rw [spherePoleDirection, linearSphereDiffeomorph_coe]
  change ‖threeSphereStereoOppositeIsometry a (L z.val)‖⁻¹ •
      threeSphereStereoOppositeIsometry a (L z.val) = _
  rw [(threeSphereStereoOppositeIsometry a).norm_map, linearSphereDiffeomorph_coe,
    map_smul]

variable (B₀ B₁ : SurgeryBallEmbedding sphereCarrier.{u})
  (hdisjoint : Disjoint (B₀.map '' Metric.ball 0 2) (B₁.map '' Metric.ball 0 2))


noncomputable def sphereTwoBallCylinder
    (D : OpenCylinderModel (sphereSecondEuclideanBall B₀ B₁ hdisjoint).closedBallᶜ) :
    OpenCylinderModel (B₀.closedBall ∪ B₁.closedBall)ᶜ :=
  pullbackCylinder (sphereTwoBallEquivalence B₀ B₁ hdisjoint) D


theorem sphereTwoBallCylinder_second_inverse
    (D : OpenCylinderModel (sphereSecondEuclideanBall B₀ B₁ hdisjoint).closedBallᶜ)
    (L : StandardCapSpace ≃L[ℝ] StandardCapSpace)
    (hinner : ∀ z : UnitTwoSphere, ∀ t : ℝ, 1 < t → t ≤ 5 / 4 →
      D.inverse ((sphereSecondEuclideanBall B₀ B₁ hdisjoint).map (t • z.val)) =
        (linearSphereDiffeomorph L z, 1 - 1 / t))
    (z : UnitTwoSphere) {t : ℝ} (ht : 1 < t) (htop : t ≤ 5 / 4) :
    (sphereTwoBallCylinder B₀ B₁ hdisjoint D).inverse (B₁.map (t • z.val)) =
      (linearSphereDiffeomorph L z, 1 - 1 / t) := by
  have hball : t • z.val ∈ Metric.ball (0 : StandardCapSpace) 2 := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (zero_lt_one.trans ht), show ‖z.val‖ = 1 by simp, mul_one]
    linarith
  change D.inverse ((sphereBallComplementEquivalence B₀).map (B₁.map (t • z.val))) = _
  exact hinner z t ht htop

variable (a : UnitThreeSphere) (L₀ : StandardCapSpace ≃L[ℝ] StandardCapSpace)
  {b : ℝ} (hb : 0 < b)
  (hcenter : (B₀.map 0).down = a)
  (hnormal : ∀ x : StandardCapSpace, ‖x‖ ≤ 5 / 4 →
    B₀.map x = ULift.up (threeSphereStereoInverse (-a) (L₀ (b • x))))

include hb hcenter hnormal in


theorem sphereTwoBall_first_ray (z : UnitTwoSphere) {t : ℝ}
    (ht : 1 < t) (htop : t < 2) (hcollapse : punctureRadialOrderIso t ≤ 5 / 4) :
    (sphereTwoBallEquivalence B₀ B₁ hdisjoint).map (B₀.map (t • z.val)) =
      ULift.up ((4 / (b * punctureRadialOrderIso t * ‖L₀ z.val‖)) •
        (spherePoleDirection a L₀ z).val) := by
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hu : 0 < punctureRadialOrderIso t := (punctureRadialOrderIso_pos_iff t).mpr ht
  have hball : t • z.val ∈ Metric.ball (0 : StandardCapSpace) 2 := by
    simpa only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht0, show ‖z.val‖ = 1 by simp, mul_one] using htop
  have hnorm : ‖punctureRadialOrderIso t • z.val‖ ≤ 5 / 4 := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hu,
      show ‖z.val‖ = 1 by simp, mul_one] using hcollapse
  rw [sphereTwoBallEquivalence_map, surgeryBallCollapse_map B₀ hball,
    punctureCollapse_ray z ht0, hnormal _ hnorm]
  apply ULift.ext
  change stereographic' 3 (B₀.map 0).down
    (threeSphereStereoInverse (-a) (L₀ (b • (punctureRadialOrderIso t • z.val)))) = _
  rw [hcenter, smul_smul, linearSphereDiffeomorph_ray]
  have hrad : 0 < b * punctureRadialOrderIso t * ‖L₀ z.val‖ :=
    mul_pos (mul_pos hb hu) (norm_pos_iff.mpr (linearSphereVector_ne_zero L₀ z))
  rw [threeSphereStereoInverse,
    threeSphereStereo_opposite_ray a (linearSphereDiffeomorph L₀ z) hrad,
    spherePoleDirection_coe]

include hb hcenter hnormal in


theorem sphereTwoBallCylinder_first_inverse
    (D : OpenCylinderModel (sphereSecondEuclideanBall B₀ B₁ hdisjoint).closedBallᶜ)
    {r R : ℝ}
    (houter : ∀ y : euclideanCarrier.{u}.carrier, R ≤ ‖y.down‖ →
      D.inverse y = (capUnitDirection y.down, 1 - r / ‖y.down‖))
    (z : UnitTwoSphere) {t : ℝ} (ht : 1 < t) (htop : t < 2)
    (hcollapse : punctureRadialOrderIso t ≤ 5 / 4)
    (hfar : R ≤ 4 / (b * punctureRadialOrderIso t * ‖L₀ z.val‖)) :
    (sphereTwoBallCylinder B₀ B₁ hdisjoint D).inverse (B₀.map (t • z.val)) =
      (spherePoleDirection a L₀ z,
        1 - r * b * punctureRadialOrderIso t * ‖L₀ z.val‖ / 4) := by
  have hu : 0 < punctureRadialOrderIso t := (punctureRadialOrderIso_pos_iff t).mpr ht
  have hrad : 0 < 4 / (b * punctureRadialOrderIso t * ‖L₀ z.val‖) :=
    div_pos (by norm_num) (mul_pos (mul_pos hb hu)
      (norm_pos_iff.mpr (linearSphereVector_ne_zero L₀ z)))
  have hnorm : ‖(4 / (b * punctureRadialOrderIso t * ‖L₀ z.val‖)) •
      (spherePoleDirection a L₀ z).val‖ =
        4 / (b * punctureRadialOrderIso t * ‖L₀ z.val‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrad,
      show ‖(spherePoleDirection a L₀ z).val‖ = 1 by simp, mul_one]
  change D.inverse ((sphereTwoBallEquivalence B₀ B₁ hdisjoint).map
    (B₀.map (t • z.val))) = _
  rw [sphereTwoBall_first_ray B₀ B₁ hdisjoint a L₀ hb hcenter hnormal z ht htop hcollapse]
  rw [houter _ (by simpa only [hnorm] using hfar)]
  change (capUnitDirection ((4 / (b * punctureRadialOrderIso t * ‖L₀ z.val‖)) •
    (spherePoleDirection a L₀ z).val),
      1 - r / ‖(4 / (b * punctureRadialOrderIso t * ‖L₀ z.val‖)) •
        (spherePoleDirection a L₀ z).val‖) = _
  rw [capUnitDirection_smul _ hrad, hnorm]
  congr 1
  congr 1
  rw [div_div_eq_mul_div]
  ring

end PoincareConjecture.M38
