import PoincareConjecture.Proofs.M38.SphereTwoBallEnds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology Filter
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {A D : GeneralizedSliceCarrier.{u}}

theorem twoBallTransport_complement (B₀ B₁ : SurgeryBallEmbedding A)
    (e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier D.carrier ∞) :
    e '' (B₀.closedBall ∪ B₁.closedBall)ᶜ =
      ((transportSurgeryBall B₀ e).closedBall ∪
        (transportSurgeryBall B₁ e).closedBall)ᶜ := by
  rw [Set.image_compl_eq (f := fun x => e x) e.bijective, Set.image_union,
    transportSurgeryBall_closedBall, transportSurgeryBall_closedBall]

noncomputable def twoBallTransportEquivalence (B₀ B₁ : SurgeryBallEmbedding A)
    (e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier D.carrier ∞) :
    SurgeryRegionEquivalence A D (B₀.closedBall ∪ B₁.closedBall)ᶜ
      ((transportSurgeryBall B₀ e).closedBall ∪
        (transportSurgeryBall B₁ e).closedBall)ᶜ where
  map := e
  inverse := e.symm
  map_image := twoBallTransport_complement B₀ B₁ e
  inverse_image := by
    rw [← twoBallTransport_complement B₀ B₁ e]
    exact e.symm_image_image _
  left_inverse := fun x _ => e.symm_apply_apply x
  right_inverse := fun y _ => e.apply_symm_apply y
  map_smooth := e.contMDiff.contMDiffOn
  inverse_smooth := e.symm.contMDiff.contMDiffOn

theorem exists_spherePole_uniform_annulus
    (L : StandardCapSpace ≃L[ℝ] StandardCapSpace) {b R : ℝ}
    (hb : 0 < b) (hR : 0 < R) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 4 ∧
      ∀ z : UnitTwoSphere, ∀ t : ℝ, 1 < t → t < 1 + ε →
        punctureRadialOrderIso t ≤ 5 / 4 ∧
          R ≤ 4 / (b * punctureRadialOrderIso t * ‖L z.val‖) := by
  let M : ℝ := ‖(L : StandardCapSpace →L[ℝ] StandardCapSpace)‖ + 1
  have hM : 0 < M := by dsimp only [M]; positivity
  let c : ℝ := min 1 (4 / (b * M * (R + 1)))
  have hc : 0 < c := by dsimp only [c]; positivity
  have hn : {t : ℝ | punctureRadialOrderIso t < c} ∈ 𝓝 (1 : ℝ) :=
    (punctureRadialOrderIso_smooth.continuous.isOpen_preimage _ isOpen_Iio).mem_nhds
      (by change punctureRadialOrderIso 1 < c
          simpa only [punctureRadialOrderIso_one] using hc)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨min δ (1 / 4), lt_min hδ (by norm_num), min_le_right _ _, ?_⟩
  intro z t ht htop
  have htball : t ∈ Metric.ball (1 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr ht)]
    have hδ' := min_le_left δ (1 / 4)
    linarith
  have huc : punctureRadialOrderIso t < c := hball htball
  have hu : 0 < punctureRadialOrderIso t := (punctureRadialOrderIso_pos_iff t).mpr ht
  have hu1 : punctureRadialOrderIso t < 1 := huc.trans_le (min_le_left _ _)
  have huR : punctureRadialOrderIso t < 4 / (b * M * (R + 1)) :=
    huc.trans_le (min_le_right _ _)
  have hprod : punctureRadialOrderIso t * (b * M * (R + 1)) < 4 :=
    (lt_div_iff₀ (by positivity)).mp huR
  have hnorm : ‖L z.val‖ ≤ M := by
    have h := (L : StandardCapSpace →L[ℝ] StandardCapSpace).le_opNorm z.val
    simp only [show ‖z.val‖ = 1 by simp, mul_one] at h
    exact h.trans (by dsimp only [M]; linarith)
  have hnormpos : 0 < ‖L z.val‖ := norm_pos_iff.mpr (linearSphereVector_ne_zero L z)
  have hq : 0 < b * punctureRadialOrderIso t * ‖L z.val‖ :=
    mul_pos (mul_pos hb hu) hnormpos
  refine ⟨hu1.le.trans (by norm_num), (le_div_iff₀ hq).mpr ?_⟩
  calc
    R * (b * punctureRadialOrderIso t * ‖L z.val‖) ≤
        (R + 1) * (b * punctureRadialOrderIso t * M) :=
      mul_le_mul (by linarith)
        (mul_le_mul_of_nonneg_left hnorm (mul_pos hb hu).le) hq.le (by positivity)
    _ ≤ 4 := by nlinarith [hprod]

theorem exists_sphereTwoBallCylinder
    (B₀ B₁ : SurgeryBallEmbedding sphereCarrier.{u})
    (hdisjoint : Disjoint (B₀.map '' Metric.ball 0 2) (B₁.map '' Metric.ball 0 2)) :
    ∃ C : OpenCylinderModel (B₀.closedBall ∪ B₁.closedBall)ᶜ,
    ∃ a : UnitThreeSphere,
    ∃ L₀ L₁ : StandardCapSpace ≃L[ℝ] StandardCapSpace,
    ∃ b r ε : ℝ,
      0 < b ∧ 0 < r ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧
      (∀ z : UnitTwoSphere, ∀ t : ℝ, 1 < t → t < 1 + ε →
        C.inverse (B₁.map (t • z.val)) = (linearSphereDiffeomorph L₁ z, 1 - 1 / t)) ∧
      (∀ z : UnitTwoSphere, ∀ t : ℝ, 1 < t → t < 1 + ε →
        C.inverse (B₀.map (t • z.val)) =
          (spherePoleDirection a L₀ z,
            1 - r * b * punctureRadialOrderIso t * ‖L₀ z.val‖ / 4)) := by
  obtain ⟨e, L₀, b, hderiv, hb, hb1, he0, hnormal, hfix⟩ :=
    exists_sphereBallPoleNormalization B₀
  let D₀ := transportSurgeryBall B₀ e
  let D₁ := transportSurgeryBall B₁ e
  let a := (B₀.map 0).down
  have hD : Disjoint (D₀.map '' Metric.ball 0 2) (D₁.map '' Metric.ball 0 2) := by
    dsimp only [D₀, D₁]
    rw [transportSurgeryBall_image, transportSurgeryBall_image]
    exact Set.disjoint_image_of_injective e.injective hdisjoint
  obtain ⟨K, L₁, r, R, hr, hrR, hinner, hinnerInv, houter, houterInv⟩ :=
    exists_centeredEuclideanBallCylinder (sphereSecondEuclideanBall D₀ D₁ hD)
  obtain ⟨ε, hε, hεtop, hann⟩ :=
    exists_spherePole_uniform_annulus L₀ hb (hr.trans hrR)
  let E := twoBallTransportEquivalence B₀ B₁ e
  let C := pullbackCylinder E (sphereTwoBallCylinder D₀ D₁ hD K)
  have hcenter : (D₀.map 0).down = a := congrArg ULift.down he0
  have hnormal' : ∀ x : StandardCapSpace, ‖x‖ ≤ 5 / 4 →
      D₀.map x = ULift.up (threeSphereStereoInverse (-a) (L₀ (b • x))) := hnormal
  refine ⟨C, a, L₀, L₁, b, r, ε, hb, hr, hε, hεtop, ?_, ?_⟩
  · intro z t ht htop
    change (sphereTwoBallCylinder D₀ D₁ hD K).inverse (D₁.map (t • z.val)) = _
    exact sphereTwoBallCylinder_second_inverse D₀ D₁ hD K L₁ hinner z ht (by linarith)
  · intro z t ht htop
    change (sphereTwoBallCylinder D₀ D₁ hD K).inverse (D₀.map (t • z.val)) = _
    obtain ⟨hcollapse, hfar⟩ := hann z t ht htop
    exact sphereTwoBallCylinder_first_inverse D₀ D₁ hD a L₀ hb hcenter hnormal'
      K houter z ht (by linarith) hcollapse hfar

end PoincareConjecture.M38
