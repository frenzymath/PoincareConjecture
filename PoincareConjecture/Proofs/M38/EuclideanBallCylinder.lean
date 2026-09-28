import PoincareConjecture.Proofs.M38.EuclideanBallNormalization
import PoincareConjecture.Proofs.M38.EllipsoidComplement
import PoincareConjecture.Proofs.M38.RoundExteriorCylinder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

attribute [local instance] threeManifoldLiftChartedSpace threeManifold_lift_isManifold

variable (B : SurgeryBallEmbedding euclideanCarrier.{u})
  (e : Diffeomorph (𝓡 3) (𝓡 3)
    euclideanCarrier.{u}.carrier euclideanCarrier.{u}.carrier ∞)
  (L : StandardCapSpace ≃L[ℝ] StandardCapSpace)
  (a : StandardCapSpace)

noncomputable def euclideanBallRoundMap (ρ : ℝ) (y : euclideanCarrier.{u}.carrier) :
    StandardCapSpace :=
  directionalRadialMap L ρ ((e y).down - a)

noncomputable def euclideanBallRoundInverse (ρ : ℝ) (x : StandardCapSpace) :
    euclideanCarrier.{u}.carrier :=
  e.symm (ULift.up (a + directionalRadialInverse L ρ x))

variable {b ρ : ℝ} (hb : 0 < b) (hρ : 0 < ρ)
  (hsize : ‖(L : StandardCapSpace →L[ℝ] StandardCapSpace)‖ * b ≤ ρ)
  (hinner : ∀ x : StandardCapSpace, ‖x‖ ≤ 5 / 4 →
    (e (B.map x)).down = a + L (b • x))

include hb hinner in

theorem euclideanBallAffine_mem_exterior {y : euclideanCarrier.{u}.carrier}
    (hy : y ∈ B.closedBallᶜ) :
    b < ‖L.symm ((e y).down - a)‖ := by
  have h : e y ∈ e '' B.closedBallᶜ := ⟨y, hy, rfl⟩
  rwa [euclideanBallAffine_complementImageAt B e L b hb a hinner] at h

include hb hρ hsize hinner

theorem euclideanBallRoundMap_mem {y : euclideanCarrier.{u}.carrier}
    (hy : y ∈ B.closedBallᶜ) :
    directionalRadialScale L * b < ‖euclideanBallRoundMap e L a ρ y‖ :=
  directionalRadialMap_mapsTo_exterior L hb hρ (hsize.trans (by nlinarith))
    (euclideanBallAffine_mem_exterior B e L a hb hinner hy)

theorem euclideanBallRoundInverse_mem {x : StandardCapSpace}
    (hx : directionalRadialScale L * b < ‖x‖) :
    euclideanBallRoundInverse e L a ρ x ∈ B.closedBallᶜ := by
  have hlin := directionalRadialInverse_mapsTo_exterior L hb hρ
    (hsize.trans (by nlinarith)) hx
  have hmem : (ULift.up (a + directionalRadialInverse L ρ x) :
      euclideanCarrier.{u}.carrier) ∈ e '' B.closedBallᶜ := by
    rw [euclideanBallAffine_complementImageAt B e L b hb a hinner]
    change b < ‖L.symm ((a + directionalRadialInverse L ρ x) - a)‖
    rwa [add_sub_cancel_left]
  obtain ⟨y, hy, heq⟩ := hmem
  change e.symm (ULift.up (a + directionalRadialInverse L ρ x)) ∈
    B.closedBallᶜ
  rw [← heq, e.symm_apply_apply]
  exact hy

theorem euclideanBallRound_left_inverse :
    Set.LeftInvOn (euclideanBallRoundMap e L a ρ)
      (euclideanBallRoundInverse e L a ρ)
      {x : StandardCapSpace | directionalRadialScale L * b < ‖x‖} := by
  intro x hx
  change directionalRadialMap L ρ
    ((e (e.symm (ULift.up (a + directionalRadialInverse L ρ x)))).down - a) = x
  rw [e.apply_symm_apply]
  simp only [ULift.down_up, add_sub_cancel_left]
  exact directionalRadial_right_inverse L hρ
    (norm_pos_iff.mp ((mul_pos (directionalRadialScale_pos L) hb).trans hx))

theorem euclideanBallRound_right_inverse :
    Set.LeftInvOn (euclideanBallRoundInverse e L a ρ)
      (euclideanBallRoundMap e L a ρ)
      B.closedBallᶜ := by
  intro y hy
  have hne := ellipsoidExterior_ne_zero L hb
    (euclideanBallAffine_mem_exterior B e L a hb hinner hy)
  change e.symm (ULift.up (a + directionalRadialInverse L ρ
    (directionalRadialMap L ρ ((e y).down - a)))) = y
  rw [directionalRadial_left_inverse L hρ hne]
  have hpoint : (ULift.up (a + ((e y).down - a)) :
      euclideanCarrier.{u}.carrier) = e y := by
    apply ULift.ext
    abel
  rw [hpoint, e.symm_apply_apply]

theorem euclideanBallRoundMap_smooth :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (euclideanBallRoundMap e L a ρ)
      B.closedBallᶜ := by
  have hc : ContMDiff (𝓡 3) (𝓡 3) ∞
      (fun y : euclideanCarrier.{u}.carrier => (e y).down - a) :=
    ((threeManifold_down_contMDiff StandardCapSpace).comp e.contMDiff).sub contMDiff_const
  have hJ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (directionalRadialMap L ρ)
      {x : StandardCapSpace | b < ‖L.symm x‖} := by
    intro x hx
    exact (directionalRadialMap_contDiffAt L
      (ellipsoidExterior_ne_zero L hb hx)).contMDiffAt.contMDiffWithinAt
  exact hJ.comp hc.contMDiffOn (fun y hy =>
    euclideanBallAffine_mem_exterior B e L a hb hinner hy)

theorem euclideanBallRoundInverse_smooth :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (euclideanBallRoundInverse e L a ρ)
      {x : StandardCapSpace | directionalRadialScale L * b < ‖x‖} := by
  have hJ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (directionalRadialInverse L ρ)
      {x : StandardCapSpace | directionalRadialScale L * b < ‖x‖} := by
    intro x hx
    exact (directionalRadialInverse_contDiffAt L (norm_pos_iff.mp
      ((mul_pos (directionalRadialScale_pos L) hb).trans hx))).contMDiffAt.contMDiffWithinAt
  exact e.symm.contMDiff.comp_contMDiffOn
    ((threeManifold_up_contMDiff StandardCapSpace).comp_contMDiffOn
      (contMDiff_const.contMDiffOn.add hJ))

noncomputable def euclideanBallRoundHomeomorph :
    ↥(B.closedBallᶜ) ≃ₜ {x : StandardCapSpace | directionalRadialScale L * b < ‖x‖} where
  toFun y := ⟨euclideanBallRoundMap e L a ρ y.val,
    euclideanBallRoundMap_mem B e L a hb hρ hsize hinner y.property⟩
  invFun x := ⟨euclideanBallRoundInverse e L a ρ x.val,
    euclideanBallRoundInverse_mem B e L a hb hρ hsize hinner x.property⟩
  left_inv y := Subtype.ext (euclideanBallRound_right_inverse B e L a hb hρ hsize hinner y.property)
  right_inv x := Subtype.ext (euclideanBallRound_left_inverse B e L a hb hρ hsize hinner x.property)
  continuous_toFun :=
    (euclideanBallRoundMap_smooth B e L a hb hρ hsize hinner).continuousOn.domRestrict.subtype_mk _
  continuous_invFun :=
    (euclideanBallRoundInverse_smooth B e L a hb hρ hsize hinner).continuousOn.domRestrict.subtype_mk _

noncomputable def euclideanBallCylinder : OpenCylinderModel B.closedBallᶜ where
  homeomorph := (roundExteriorHomeomorph (mul_pos (directionalRadialScale_pos L) hb)).trans
    (euclideanBallRoundHomeomorph B e L a hb hρ hsize hinner).symm
  coordinate := euclideanBallRoundInverse e L a ρ ∘
    roundExteriorCoordinate (directionalRadialScale L * b)
  coordinate_eq _ := rfl
  coordinate_smooth :=
    (euclideanBallRoundInverse_smooth B e L a hb hρ hsize hinner).comp
      roundExteriorCoordinate_smooth
      (fun _ hz => roundExteriorCoordinate_mem (mul_pos (directionalRadialScale_pos L) hb) hz)
  inverse := roundExteriorInverse (directionalRadialScale L * b) ∘
    euclideanBallRoundMap e L a ρ
  inverse_mem _ hy := roundExteriorInverse_mem (mul_pos (directionalRadialScale_pos L) hb)
    (euclideanBallRoundMap_mem B e L a hb hρ hsize hinner hy)
  left_inverse := by
    intro z hz
    change roundExteriorInverse (directionalRadialScale L * b)
      (euclideanBallRoundMap e L a ρ (euclideanBallRoundInverse e L a ρ
        (roundExteriorCoordinate (directionalRadialScale L * b) z))) = z
    rw [euclideanBallRound_left_inverse B e L a hb hρ hsize hinner
      (roundExteriorCoordinate_mem (mul_pos (directionalRadialScale_pos L) hb) hz)]
    exact roundExterior_left_inverse (mul_pos (directionalRadialScale_pos L) hb) hz
  right_inverse := by
    intro y hy
    change euclideanBallRoundInverse e L a ρ
      (roundExteriorCoordinate (directionalRadialScale L * b)
        (roundExteriorInverse (directionalRadialScale L * b)
          (euclideanBallRoundMap e L a ρ y))) = y
    rw [roundExterior_right_inverse (mul_pos (directionalRadialScale_pos L) hb)
      (euclideanBallRoundMap_mem B e L a hb hρ hsize hinner hy)]
    exact euclideanBallRound_right_inverse B e L a hb hρ hsize hinner hy
  inverse_smooth :=
    (roundExteriorInverse_smooth (mul_pos (directionalRadialScale_pos L) hb)).comp
      (euclideanBallRoundMap_smooth B e L a hb hρ hsize hinner)
      (fun _ hy => euclideanBallRoundMap_mem B e L a hb hρ hsize hinner hy)

theorem euclideanBallCylinder_coordinate (z : RoundCylinderSpace) :
    (euclideanBallCylinder B e L a hb hρ hsize hinner).coordinate z =
      e.symm (ULift.up (a + directionalRadialInverse L ρ
        (roundExteriorCoordinate (directionalRadialScale L * b) z))) := rfl

theorem euclideanBallCylinder_inverse (y : euclideanCarrier.{u}.carrier) :
    (euclideanBallCylinder B e L a hb hρ hsize hinner).inverse y =
      roundExteriorInverse (directionalRadialScale L * b)
        (directionalRadialMap L ρ ((e y).down - a)) := rfl

theorem euclideanBallCylinder_inner_inverse (z : UnitTwoSphere) {t : ℝ}
    (ht : 1 < t) (htop : t ≤ 5 / 4) :
    (euclideanBallCylinder B e L a hb hρ hsize hinner).inverse (B.map (t • z.val)) =
      (linearSphereDiffeomorph L z, 1 - 1 / t) := by
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hz : ‖t • z.val‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, show ‖z.val‖ = 1 by simp, mul_one]
  have hbound : ‖L ((b * t) • z.val)‖ ≤ (5 / 4) * ρ := by
    calc
      ‖L ((b * t) • z.val)‖ ≤
          ‖(L : StandardCapSpace →L[ℝ] StandardCapSpace)‖ * ‖(b * t) • z.val‖ :=
        (L : StandardCapSpace →L[ℝ] StandardCapSpace).le_opNorm _
      _ = (‖(L : StandardCapSpace →L[ℝ] StandardCapSpace)‖ * b) * t := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hb ht0),
          show ‖z.val‖ = 1 by simp, mul_one]
        ring
      _ ≤ ρ * t := mul_le_mul_of_nonneg_right hsize ht0.le
      _ ≤ (5 / 4) * ρ := by nlinarith
  rw [euclideanBallCylinder_inverse, hinner _ (hz.trans_le htop),
    add_sub_cancel_left, smul_smul,
    directionalRadialMap_linear_ray L hρ z (mul_pos hb ht0) hbound]
  have hrad : directionalRadialScale L * b < directionalRadialScale L * (b * t) := by
    nlinarith [mul_pos (directionalRadialScale_pos L) hb]
  have h := roundExteriorCylinder_radial_inverse
    (mul_pos (directionalRadialScale_pos L) hb) (linearSphereDiffeomorph L z) hrad
  change roundExteriorInverse (directionalRadialScale L * b)
    ((directionalRadialScale L * (b * t)) • (linearSphereDiffeomorph L z).val) =
      (linearSphereDiffeomorph L z, 1 - 1 / t)
  change roundExteriorInverse (directionalRadialScale L * b)
    ((directionalRadialScale L * (b * t)) • (linearSphereDiffeomorph L z).val) =
      (linearSphereDiffeomorph L z, 1 - (directionalRadialScale L * b) /
        (directionalRadialScale L * (b * t))) at h
  rw [h]
  congr 2
  field_simp [hb.ne', ht0.ne', (directionalRadialScale_pos L).ne'] <;> ring

theorem euclideanBallCylinder_inner_coordinate (z : UnitTwoSphere) {t : ℝ}
    (ht : 1 < t) (htop : t ≤ 5 / 4) :
    (euclideanBallCylinder B e L a hb hρ hsize hinner).coordinate
      (linearSphereDiffeomorph L z, 1 - 1 / t) = B.map (t • z.val) := by
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hz : ‖t • z.val‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, show ‖z.val‖ = 1 by simp, mul_one]
  have hmem : B.map (t • z.val) ∈ B.closedBallᶜ := by
    rintro ⟨x, hx, heq⟩
    have hx2 : x ∈ Metric.ball (0 : StandardCapSpace) 2 :=
      (Metric.closedBall_subset_ball (by norm_num)) hx
    have ht2 : t • z.val ∈ Metric.ball (0 : StandardCapSpace) 2 := by
      simp only [Metric.mem_ball, dist_zero_right, hz]
      linarith
    have heq' : x = t • z.val := B.left_inverse.injOn hx2 ht2 heq
    have hxnorm : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    rw [heq', hz] at hxnorm
    exact (not_le.mpr ht) hxnorm
  rw [← euclideanBallCylinder_inner_inverse B e L a hb hρ hsize hinner z ht htop]
  exact (euclideanBallCylinder B e L a hb hρ hsize hinner).right_inverse hmem

theorem euclideanBallCylinder_outer_inverse (y : euclideanCarrier.{u}.carrier)
    (hfix : e y = y) (hy : (3 / 2) * ρ ≤ ‖y.down - a‖) :
    (euclideanBallCylinder B e L a hb hρ hsize hinner).inverse y =
      (capUnitDirection (y.down - a),
        1 - (directionalRadialScale L * b) / ‖y.down - a‖) := by
  rw [euclideanBallCylinder_inverse, hfix, directionalRadialMap_outer L hρ hy]
  rfl

theorem euclideanBallCylinder_outer_coordinate (z : UnitTwoSphere) (s : ℝ)
    (hfix : e (ULift.up (a +
      (directionalRadialScale L * b / (1 - s)) • z.val)) =
        ULift.up (a + (directionalRadialScale L * b / (1 - s)) • z.val))
    (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hfar : (3 / 2) * ρ ≤ directionalRadialScale L * b / (1 - s)) :
    (euclideanBallCylinder B e L a hb hρ hsize hinner).coordinate (z, s) =
      ULift.up (a + (directionalRadialScale L * b / (1 - s)) • z.val) := by
  have hnorm := roundExteriorCoordinate_norm (mul_pos (directionalRadialScale_pos L) hb)
    (show (z, s) ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) 1 from ⟨Set.mem_univ _, hs⟩)
  rw [euclideanBallCylinder_coordinate, directionalRadialInverse_outer L hρ (hnorm.symm ▸ hfar)]
  change e.symm (ULift.up (a +
    (directionalRadialScale L * b / (1 - s)) • z.val)) = _
  simpa only [e.symm_apply_apply] using (congrArg (fun y => e.symm y) hfix).symm

end PoincareConjecture.M38
