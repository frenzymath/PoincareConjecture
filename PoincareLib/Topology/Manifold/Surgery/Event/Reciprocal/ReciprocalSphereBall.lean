import PoincareLib.Topology.Manifold.Surgery.Event.Reciprocal.ReciprocalBallAnnuli
import PoincareLib.Topology.Manifold.Surgery.Event.Sphere.SphereExteriorBall
import PoincareLib.Topology.Manifold.Surgery.Event.Linear.LinearSphereDiffeomorph

/-!
# The reciprocal opposite sphere ball with its original attaching frame

The actual opposite stereographic chart is precomposed with the explicit
outer radial diffeomorphism. Its complement is the reference chart's
radius-three-halves ball. The literal chart transition determines the
sphere gluing map and the full positive attaching formula.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

attribute [local instance] threeManifoldLiftChartedSpace threeManifold_lift_isManifold

private instance sphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

variable (p : sphereCarrier.{u}.carrier)

/-- The actual angular frame goes from the opposite chart to the original reference chart. -/
noncomputable def reciprocalSphereDirection :
    Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞ :=
  linearSphereDiffeomorph (threeSphereStereoOppositeIsometry (-p.down)).toContinuousLinearEquiv

/-- Orthogonality leaves no normalization factor in the actual angular vector. -/
theorem reciprocalSphereDirection_coe (z : UnitTwoSphere) :
    (reciprocalSphereDirection p z).val =
      threeSphereStereoOppositeIsometry (-p.down) z.val := by
  rw [reciprocalSphereDirection, linearSphereDiffeomorph_coe]
  change ‖threeSphereStereoOppositeIsometry (-p.down) z.val‖⁻¹ •
    threeSphereStereoOppositeIsometry (-p.down) z.val = _
  rw [(threeSphereStereoOppositeIsometry (-p.down)).norm_map,
    show ‖z.val‖ = 1 by simp, inv_one, one_smul]

/-- The inverse angular vector uses the actual inverse frame, without an involution assumption. -/
theorem reciprocalSphereDirection_symm_coe (z : UnitTwoSphere) :
    ((reciprocalSphereDirection p).symm z).val =
      (threeSphereStereoOppositeIsometry (-p.down)).symm z.val := by
  rw [reciprocalSphereDirection, linearSphereDiffeomorph_symm_coe]
  change ‖(threeSphereStereoOppositeIsometry (-p.down)).symm z.val‖⁻¹ •
    (threeSphereStereoOppositeIsometry (-p.down)).symm z.val = _
  rw [(threeSphereStereoOppositeIsometry (-p.down)).symm.norm_map,
    show ‖z.val‖ = 1 by simp, inv_one, one_smul]

/-- Opposite inverse charts have the exact positive-ray equation in the original reference frame. -/
theorem spherePoleReference_opposite_ray (z : UnitTwoSphere) {r : ℝ} (hr : 0 < r) :
    spherePunctureInverse p (ULift.up (r • z.val)) =
      (spherePoleReferenceBall p).map
        ((4 / r) • threeSphereStereoOppositeIsometry (-p.down) z.val) := by
  have hne : spherePunctureInverse p (ULift.up (r • z.val)) ≠ ULift.up (-p.down) := by
    intro heq
    have hzero := spherePunctureInverse_zero p
    have hinj := (spherePuncture_right_inverse p).injOn
      (Set.mem_univ (ULift.up (r • z.val))) (Set.mem_univ (ULift.up 0))
        (heq.trans hzero.symm)
    exact (smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere z)) (congrArg ULift.down hinj)
  have hchart :
      (spherePunctureMap (ULift.up (-p.down))
        (spherePunctureInverse p (ULift.up (r • z.val)))).down =
          (4 / r) • threeSphereStereoOppositeIsometry (-p.down) z.val := by
    change stereographic' 3 (-p.down) ((stereographic' 3 p.down).symm (r • z.val)) = _
    simpa only [neg_neg] using threeSphereStereo_opposite_ray (-p.down) z hr
  have hcoord :
      spherePunctureMap (ULift.up (-p.down))
        (spherePunctureInverse p (ULift.up (r • z.val))) =
          ULift.up ((4 / r) • threeSphereStereoOppositeIsometry (-p.down) z.val) :=
    ULift.ext _ _ hchart
  have hleft := spherePuncture_left_inverse (ULift.up (-p.down)) hne
  rw [hcoord] at hleft
  exact hleft.symm

variable {a : ℝ} (ha : 0 < a) (ha8 : a ≤ 1 / 8)

/-- The actual opposite ball uses the original puncture chart and the full reciprocal radial map. -/
noncomputable def reciprocalSphereBall : SurgeryBallEmbedding sphereCarrier.{u} := by
  let e := reciprocalOuterBallDiffeomorph ha ha8
  let f : StandardCapSpace → sphereCarrier.{u}.carrier :=
    fun x => spherePunctureInverse p (ULift.up (e x))
  let g : sphereCarrier.{u}.carrier → StandardCapSpace :=
    fun y => e.symm (spherePunctureMap p y).down
  have hup : ContMDiff (𝓡 3) (𝓡 3) ∞
      (fun x : StandardCapSpace => (ULift.up (e x) : euclideanCarrier.{u}.carrier)) :=
    (threeManifold_up_contMDiff StandardCapSpace).comp e.contMDiff
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f := (spherePunctureInverse_smooth p).comp hup
  have hsub : f '' Metric.ball 0 2 ⊆ ({p} : Set sphereCarrier.{u}.carrier)ᶜ := by
    rintro _ ⟨x, _, rfl⟩
    exact spherePunctureInverse_ne p (ULift.up (e x))
  have hg : ContMDiffOn (𝓡 3) (𝓡 3) ∞ g (f '' Metric.ball 0 2) :=
    e.symm.contMDiff.comp_contMDiffOn
      ((threeManifold_down_contMDiff StandardCapSpace).comp_contMDiffOn
        ((spherePunctureMap_smooth p).mono hsub))
  have hleft : Set.LeftInvOn g f (Metric.ball 0 2) := by
    intro x _
    change e.symm (spherePunctureMap p (spherePunctureInverse p (ULift.up (e x)))).down = x
    rw [spherePuncture_right_inverse p (Set.mem_univ _)]
    exact e.symm_apply_apply x
  exact {
    map := f
    inverse := g
    map_smooth := hf.contMDiffOn
    inverse_smooth := hg
    left_inverse := hleft
    right_inverse := by
      rintro _ ⟨x, hx, rfl⟩
      exact congrArg f (hleft hx)
    open_embedding := smooth_left_inverse_openEmbedding Metric.isOpen_ball
      hf.contMDiffOn hg hleft }

/-- The actual total forward map retains the literal outer radial coordinates. -/
theorem reciprocalSphereBall_map (x : StandardCapSpace) :
    (reciprocalSphereBall p ha ha8).map x =
      spherePunctureInverse p (ULift.up (reciprocalOuterBallDiffeomorph ha ha8 x)) := rfl

/-- The total inverse retains the original puncture chart followed by the actual radial inverse. -/
theorem reciprocalSphereBall_inverse (y : sphereCarrier.{u}.carrier) :
    (reciprocalSphereBall p ha ha8).inverse y =
      (reciprocalOuterBallDiffeomorph ha ha8).symm (spherePunctureMap p y).down := rfl

/-- The actual center is the antipode of the original reference center. -/
theorem reciprocalSphereBall_center :
    (reciprocalSphereBall p ha ha8).map 0 = ULift.up (-p.down) := by
  have hezero : reciprocalOuterBallDiffeomorph ha ha8 0 = 0 := by
    apply norm_eq_zero.mp
    rw [reciprocalOuterBallDiffeomorph_norm]
    simp
  rw [reciprocalSphereBall_map, hezero, spherePunctureInverse_zero]

/-- The exact radial closed image gives the original scale-eight-thirds opposite closed ball. -/
theorem reciprocalSphereBall_closedBall :
    (reciprocalSphereBall p ha ha8).closedBall =
      (sphereScaledPoleBall (ULift.up (-p.down)) (8 / 3) (by norm_num)).closedBall := by
  have himage : (reciprocalSphereBall p ha ha8).closedBall =
      (fun x : StandardCapSpace => spherePunctureInverse p (ULift.up x)) ''
        Metric.closedBall 0 (8 / 3) := by
    change ((fun x : StandardCapSpace => spherePunctureInverse p (ULift.up x)) ∘
      reciprocalOuterBallDiffeomorph ha ha8) '' Metric.closedBall 0 1 = _
    rw [Set.image_comp, reciprocalOuterBallDiffeomorph_closedBall]
  ext y
  rw [himage, sphereScaledPoleBall_mem_closed_iff]
  simp only [ULift.down_up, neg_neg, ULift.up_down]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨spherePunctureInverse_ne p _, ?_⟩
    rw [spherePuncture_right_inverse p (Set.mem_univ _)]
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  · rintro ⟨hy, hnorm⟩
    refine ⟨(spherePunctureMap p y).down, ?_, spherePuncture_left_inverse p hy⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm

/-- The closed-ball complement is exactly the original reference radius-three-halves open image. -/
theorem reciprocalSphereBall_complement :
    (reciprocalSphereBall p ha ha8).closedBallᶜ =
      (spherePoleReferenceBall p).map '' Metric.ball 0 (3 / 2) := by
  rw [reciprocalSphereBall_closedBall, sphereScaledPoleBall_complement]
  norm_num <;> rfl

/-- The entire opposite chart lies in a scale-three closed ball in that same opposite chart. -/
theorem reciprocalSphereBall_full_inside :
    (reciprocalSphereBall p ha ha8).map '' Metric.ball 0 2 ⊆
      (sphereScaledPoleBall (ULift.up (-p.down)) 3 (by norm_num)).closedBall := by
  rintro _ ⟨x, hx, rfl⟩
  rw [reciprocalSphereBall_map, sphereScaledPoleBall_mem_closed_iff]
  simp only [ULift.down_up, neg_neg, ULift.up_down]
  refine ⟨spherePunctureInverse_ne p _, ?_⟩
  rw [spherePuncture_right_inverse p (Set.mem_univ _)]
  have h := reciprocalOuterBallDiffeomorph_bound ha ha8 hx
  change ‖reciprocalOuterBallDiffeomorph ha ha8 x‖ ≤ 3
  linarith

/-- The full opposite chart is disjoint from the original reference open unit image. -/
theorem reciprocalSphereBall_full_disjoint :
    Disjoint ((reciprocalSphereBall p ha ha8).map '' Metric.ball 0 2)
      ((spherePoleReferenceBall p).map '' Metric.ball 0 1) := by
  let H := sphereScaledPoleBall (ULift.up (-p.down)) 3 (by norm_num)
  have hinner : (spherePoleReferenceBall p).map '' Metric.ball 0 1 ⊆ H.closedBallᶜ := by
    change (spherePoleReferenceBall p).map '' Metric.ball 0 1 ⊆
      (sphereScaledPoleBall (ULift.up (-p.down)) 3 (by norm_num)).closedBallᶜ
    rw [sphereScaledPoleBall_complement]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, Metric.ball_subset_ball (by norm_num) hx, rfl⟩
  exact Set.disjoint_left.mpr (fun _ hy hz =>
    hinner hz (reciprocalSphereBall_full_inside p ha ha8 hy))

/-- The positive full attaching annulus agrees exactly with the reciprocal continuation
in the original reference chart and its original angular frame. -/
theorem reciprocalSphereBall_positive (z : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    (reciprocalSphereBall p ha ha8).map
      ((1 + s) • ((reciprocalSphereDirection p).symm z).val) =
        (spherePoleReferenceBall p).map
          (((3 / 2) * ((1 + a * s / 2) / (1 + a * s))) • z.val) := by
  have hmul : 0 < a * s := mul_pos ha hs.1
  have hnum : 0 < 1 + a * s := by linarith
  have hden : 0 < 1 + a * s / 2 := by linarith
  have hrad : 0 < (8 / 3 : ℝ) * ((1 + a * s) / (1 + a * s / 2)) :=
    mul_pos (by norm_num) (div_pos hnum hden)
  rw [reciprocalSphereBall_map,
    reciprocalOuterBallDiffeomorph_positive ha ha8 ((reciprocalSphereDirection p).symm z) hs,
    spherePoleReference_opposite_ray p ((reciprocalSphereDirection p).symm z) hrad,
    reciprocalSphereDirection_symm_coe,
    (threeSphereStereoOppositeIsometry (-p.down)).apply_symm_apply]
  congr 2
  field_simp [hnum.ne', hden.ne', show 2 + a * s ≠ 0 by linarith] <;> ring

end PoincareMT.M38
