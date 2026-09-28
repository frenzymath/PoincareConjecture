import PoincareConjecture.Proofs.M38.ReciprocalEnclosingBall
import PoincareConjecture.Proofs.M38.ReciprocalSphereBall
import PoincareConjecture.Proofs.M38.PolarCoordinates











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

private noncomputable def reciprocalInnerShellDiffeomorph :
    Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞ :=
  reciprocalInnerRadial.trans
    ((LinearEquiv.smulOfNeZero ℝ StandardCapSpace (3 / 2 : ℝ)
      (by norm_num)).toContinuousLinearEquiv.toDiffeomorph)

private theorem reciprocalInnerShellDiffeomorph_apply (x : StandardCapSpace) :
    reciprocalInnerShellDiffeomorph x = (3 / 2 : ℝ) • reciprocalInnerRadial x := rfl

private theorem reciprocalInnerShellDiffeomorph_norm (x : StandardCapSpace) :
    ‖reciprocalInnerShellDiffeomorph x‖ = (3 / 2) * reciprocalInnerOrderIso ‖x‖ := by
  rw [reciprocalInnerShellDiffeomorph_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2), reciprocalInnerRadial_norm]

private theorem reciprocalInnerOrderIso_seven_eighths :
    reciprocalInnerOrderIso (7 / 8) = 17 / 18 := by
  have h := reciprocalInnerOrderIso_annulus (s := 1 / 8) (by norm_num)
  norm_num at h
  exact h

private theorem reciprocalCollar_lt_one {a : ℝ} (ha8 : a ≤ 1 / 8) : a < 1 := by
  linarith

private theorem reciprocalInnerShell_bounds {a : ℝ} (ha : 0 < a) (ha8 : a ≤ 1 / 8)
    {z : RoundCylinderSpace} (hz : z ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :
    17 / 12 < ‖reciprocalInnerShellDiffeomorph (capShellMap 1 a z)‖ ∧
      ‖reciprocalInnerShellDiffeomorph (capShellMap 1 a z)‖ < 45 / 28 := by
  have h := capShell_mem ha (reciprocalCollar_lt_one ha8) hz
  have hlo : 7 / 8 < ‖capShellMap 1 a z‖ := by linarith [h.1]
  have hhi : ‖capShellMap 1 a z‖ < 9 / 8 := by linarith [h.2]
  have hl := reciprocalInnerOrderIso.strictMono hlo
  have hu := reciprocalInnerOrderIso.strictMono hhi
  rw [reciprocalInnerOrderIso_seven_eighths] at hl
  rw [reciprocalInnerOrderIso_nine_eighths] at hu
  rw [reciprocalInnerShellDiffeomorph_norm]
  constructor <;> linarith

variable {A : GeneralizedSliceCarrier.{u}}


noncomputable def reciprocalEnclosingCollarMap (C : SurgeryBallEmbedding A) (a : ℝ)
    (z : RoundCylinderSpace) : A.carrier :=
  C.map (reciprocalInnerShellDiffeomorph (capShellMap 1 a z))


noncomputable def reciprocalEnclosingCollarInverse (C : SurgeryBallEmbedding A) (a : ℝ)
    (y : A.carrier) : RoundCylinderSpace :=
  capShellInverse 1 a (reciprocalInnerShellDiffeomorph.symm (C.inverse y))

variable (C : SurgeryBallEmbedding A) {a : ℝ} (ha : 0 < a) (ha8 : a ≤ 1 / 8)

include ha ha8


theorem reciprocalEnclosingCollar_coordinate_mem {z : RoundCylinderSpace}
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :
    reciprocalInnerShellDiffeomorph (capShellMap 1 a z) ∈ Metric.ball 0 2 := by
  rw [Metric.mem_ball, dist_zero_right]
  have h := (reciprocalInnerShell_bounds ha ha8 hz).2
  linarith


theorem reciprocalEnclosingCollar_coordinates {z : RoundCylinderSpace}
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :
    C.inverse (reciprocalEnclosingCollarMap C a z) =
      reciprocalInnerShellDiffeomorph (capShellMap 1 a z) :=
  C.left_inverse (reciprocalEnclosingCollar_coordinate_mem ha ha8 hz)


theorem reciprocalEnclosingCollar_norm_bounds {z : RoundCylinderSpace}
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :
    17 / 12 < ‖C.inverse (reciprocalEnclosingCollarMap C a z)‖ ∧
      ‖C.inverse (reciprocalEnclosingCollarMap C a z)‖ < 45 / 28 := by
  rw [reciprocalEnclosingCollar_coordinates C ha ha8 hz]
  exact reciprocalInnerShell_bounds ha ha8 hz


theorem reciprocalEnclosingCollar_left_inverse :
    Set.LeftInvOn (reciprocalEnclosingCollarInverse C a) (reciprocalEnclosingCollarMap C a)
      (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) := by
  intro z hz
  change capShellInverse 1 a (reciprocalInnerShellDiffeomorph.symm
    (C.inverse (reciprocalEnclosingCollarMap C a z))) = z
  rw [reciprocalEnclosingCollar_coordinates C ha ha8 hz,
    reciprocalInnerShellDiffeomorph.symm_apply_apply]
  exact capShell_left_inverse ha (reciprocalCollar_lt_one ha8) hz


theorem reciprocalEnclosingCollar_smooth :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (reciprocalEnclosingCollarMap C a)
      (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :=
  C.map_smooth.comp
    (reciprocalInnerShellDiffeomorph.contMDiff.comp (capShellMap_smooth 1 a)).contMDiffOn
      (fun _ hz => reciprocalEnclosingCollar_coordinate_mem ha ha8 hz)


theorem reciprocalEnclosingCollar_inverse_smooth :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (reciprocalEnclosingCollarInverse C a)
      (reciprocalEnclosingCollarMap C a '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) := by
  have hsub : reciprocalEnclosingCollarMap C a '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) ⊆
      C.map '' Metric.ball 0 2 := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨_, reciprocalEnclosingCollar_coordinate_mem ha ha8 hz, rfl⟩
  apply (capShellInverse_smooth 1 a).comp
    (reciprocalInnerShellDiffeomorph.symm.contMDiff.comp_contMDiffOn
      (C.inverse_smooth.mono hsub))
  rintro _ ⟨z, hz, rfl⟩
  change reciprocalInnerShellDiffeomorph.symm
    (C.inverse (reciprocalEnclosingCollarMap C a z)) ≠ 0
  rw [reciprocalEnclosingCollar_coordinates C ha ha8 hz,
    reciprocalInnerShellDiffeomorph.symm_apply_apply]
  apply norm_pos_iff.mp
  have h := (capShell_mem ha (reciprocalCollar_lt_one ha8) hz).1
  linarith


theorem reciprocalEnclosingCollar_open :
    IsOpen (reciprocalEnclosingCollarMap C a '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) := by
  let S : Set StandardCapSpace := {x | 1 - a < ‖x‖ ∧ ‖x‖ < 1 + a}
  have hS : IsOpen S := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hV : IsOpen (reciprocalInnerShellDiffeomorph '' S) :=
    reciprocalInnerShellDiffeomorph.toHomeomorph.isOpenMap S hS
  have hsub : reciprocalInnerShellDiffeomorph '' S ⊆ Metric.ball 0 2 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ capShellMap 1 a '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) := by
      rw [capShell_image ha (reciprocalCollar_lt_one ha8)]
      exact hx
    obtain ⟨z, hz, rfl⟩ := hx'
    exact reciprocalEnclosingCollar_coordinate_mem ha ha8 hz
  change IsOpen ((C.map ∘ reciprocalInnerShellDiffeomorph ∘ capShellMap 1 a) '' _)
  rw [Set.image_comp, Set.image_comp, capShell_image ha (reciprocalCollar_lt_one ha8)]
  exact smooth_left_inverse_image_open Metric.isOpen_ball C.map_smooth C.inverse_smooth
    C.left_inverse hV hsub


noncomputable def reciprocalEnclosingCollar :
    PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) RoundCylinderSpace A.carrier ∞ where
  toFun := reciprocalEnclosingCollarMap C a
  invFun := reciprocalEnclosingCollarInverse C a
  source := Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1
  target := reciprocalEnclosingCollarMap C a '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)
  map_source' := fun z hz => ⟨z, hz, rfl⟩
  map_target' := by
    rintro y ⟨z, hz, rfl⟩
    rw [reciprocalEnclosingCollar_left_inverse C ha ha8 hz]
    exact hz
  left_inv' := reciprocalEnclosingCollar_left_inverse C ha ha8
  right_inv' := by
    rintro y ⟨z, hz, rfl⟩
    exact congrArg (reciprocalEnclosingCollarMap C a)
      (reciprocalEnclosingCollar_left_inverse C ha ha8 hz)
  open_source := isOpen_univ.prod isOpen_Ioo
  open_target := reciprocalEnclosingCollar_open C ha ha8
  contMDiffOn_toFun := reciprocalEnclosingCollar_smooth C ha ha8
  contMDiffOn_invFun := reciprocalEnclosingCollar_inverse_smooth C ha ha8


theorem reciprocalEnclosingCollar_source :
    (reciprocalEnclosingCollar C ha ha8).source = Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 := rfl


theorem reciprocalEnclosingCollar_apply (z : RoundCylinderSpace) :
    reciprocalEnclosingCollar C ha ha8 z = reciprocalEnclosingCollarMap C a z := rfl


theorem reciprocalEnclosingCollar_inverse (y : A.carrier) :
    (reciprocalEnclosingCollar C ha ha8).symm y = reciprocalEnclosingCollarInverse C a y := rfl


theorem reciprocalEnclosingCollar_coordinate_formula {z : RoundCylinderSpace}
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :
    C.inverse (reciprocalEnclosingCollarMap C a z) =
      ((3 / 2) * ((1 + a * z.2 / 2) / (1 + a * z.2))) • z.1.val := by
  have hrad : 0 < 1 - a * z.2 := by
    have h := mul_lt_mul_of_pos_left hz.2.2 ha
    linarith
  have hsmall : |a * z.2| ≤ 1 / 8 := by
    rw [abs_mul, abs_of_pos ha]
    have h := mul_lt_mul_of_pos_left (abs_lt.mpr hz.2) ha
    linarith
  rw [reciprocalEnclosingCollar_coordinates C ha ha8 hz,
    reciprocalInnerShellDiffeomorph_apply]
  change (3 / 2 : ℝ) • reciprocalInnerRadial ((1 - a * z.2) • z.1.val) = _
  rw [reciprocalInnerRadial_ray z.1 hrad, reciprocalInnerOrderIso_annulus hsmall, smul_smul]


theorem reciprocalEnclosingCollar_formula {z : RoundCylinderSpace}
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :
    reciprocalEnclosingCollarMap C a z =
      C.map (((3 / 2) * ((1 + a * z.2 / 2) / (1 + a * z.2))) • z.1.val) := by
  have h := reciprocalEnclosingCollar_coordinate_formula C ha ha8 hz
  rw [reciprocalEnclosingCollar_coordinates C ha ha8 hz] at h
  exact congrArg C.map h


theorem reciprocalEnclosingCollar_negative (z : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Set.Ioo (-1 : ℝ) 0) :
    reciprocalEnclosingCollar C ha ha8 (z, s) =
      (reciprocalEnclosingBall C ha ha8).map ((1 - s) • z.val) := by
  rw [reciprocalEnclosingCollar_apply,
    reciprocalEnclosingCollar_formula C ha ha8
      (show (z, s) ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 from
        ⟨Set.mem_univ _, hs.1, by linarith [hs.2]⟩),
    reciprocalEnclosingBall_negative C ha ha8 z hs]


theorem reciprocalEnclosingCollar_positive_reference (p : sphereCarrier.{u}.carrier)
    (z : UnitTwoSphere) {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    (spherePoleReferenceBall p).map
      (C.inverse (reciprocalEnclosingCollar C ha ha8 (z, s))) =
        (reciprocalSphereBall p ha ha8).map
          ((1 + s) • ((reciprocalSphereDirection p).symm z).val) := by
  rw [reciprocalEnclosingCollar_apply,
    reciprocalEnclosingCollar_coordinate_formula C ha ha8
      (show (z, s) ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 from
        ⟨Set.mem_univ _, by linarith [hs.1], hs.2⟩),
    reciprocalSphereBall_positive p ha ha8 z hs]


theorem reciprocalEnclosingCollar_zero (z : UnitTwoSphere) :
    reciprocalEnclosingCollar C ha ha8 (z, 0) = C.map ((3 / 2 : ℝ) • z.val) := by
  rw [reciprocalEnclosingCollar_apply]
  simpa using reciprocalEnclosingCollar_formula C ha ha8
    (show (z, 0) ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 by constructor <;> simp)


theorem reciprocalEnclosingCollar_central :
    reciprocalEnclosingCollar C ha ha8 '' (Set.univ ×ˢ ({0} : Set ℝ)) =
      C.map '' Metric.sphere 0 (3 / 2) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨⟨z, s⟩, hz, rfl⟩
    have hs : s = 0 := hz.2
    rw [hs, reciprocalEnclosingCollar_zero C ha ha8 z]
    refine ⟨(3 / 2 : ℝ) • z.val, ?_, rfl⟩
    simp [norm_smul]
  · rintro _ ⟨x, hx, rfl⟩
    have hnorm : ‖x‖ = 3 / 2 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hx
    refine ⟨(capUnitDirection x, 0), ⟨Set.mem_univ _, rfl⟩, ?_⟩
    rw [reciprocalEnclosingCollar_zero C ha ha8, ← hnorm, capUnitDirection_radial]


theorem reciprocalEnclosingCollar_full_disjoint_unit :
    Disjoint (reciprocalEnclosingCollar C ha ha8 '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1))
      (C.map '' Metric.ball 0 1) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨z, hz, rfl⟩ ⟨x, hx, heq⟩
  have heq' := congrArg C.inverse heq
  rw [C.left_inverse (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hx)] at heq'
  have hnorm : ‖x‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hbound := (reciprocalEnclosingCollar_norm_bounds C ha ha8 hz).1
  change x = C.inverse (reciprocalEnclosingCollarMap C a z) at heq'
  rw [← heq'] at hbound
  linarith


theorem reciprocalEnclosingCollar_central_disjoint :
    Disjoint (reciprocalEnclosingCollar C ha ha8 '' (Set.univ ×ˢ ({0} : Set ℝ)))
      ((C.map '' Metric.ball 0 (3 / 2)) ∪ (reciprocalEnclosingBall C ha ha8).closedBallᶜ) := by
  rw [reciprocalEnclosingCollar_central]
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, hx, rfl⟩ (hinner | houter)
  · obtain ⟨y, hy, heq⟩ := hinner
    have hxnorm : ‖x‖ = 3 / 2 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hx
    have hxball : x ∈ Metric.ball 0 2 := by
      simp only [Metric.mem_ball, dist_zero_right, hxnorm]
      norm_num
    have hyball : y ∈ Metric.ball 0 2 := Metric.ball_subset_ball (by norm_num) hy
    have hyx : y = x := C.left_inverse.injOn hyball hxball heq
    have hynorm : ‖y‖ < 3 / 2 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hy
    rw [hyx, hxnorm] at hynorm
    exact (lt_irrefl _ hynorm)
  · apply houter
    rw [reciprocalEnclosingBall_closedBall]
    refine ⟨x, ?_, rfl⟩
    have hxnorm : ‖x‖ = 3 / 2 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hx
    simpa only [Metric.mem_closedBall, dist_zero_right, hxnorm] using
      (le_rfl : (3 / 2 : ℝ) ≤ 3 / 2)

end PoincareConjecture.M38
