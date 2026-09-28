import PoincareConjecture.Proofs.M38.PolarCoordinates









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38


noncomputable def roundExteriorCoordinate (r : ℝ) (z : RoundCylinderSpace) : StandardCapSpace :=
  (r / (1 - z.2)) • z.1.val


noncomputable def roundExteriorInverse (r : ℝ) (x : StandardCapSpace) : RoundCylinderSpace :=
  (capUnitDirection x, 1 - r / ‖x‖)

variable {r : ℝ} (hr : 0 < r)

include hr


theorem roundExterior_radius_gt {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    r < r / (1 - s) := by
  apply (lt_div_iff₀ (sub_pos.mpr hs.2)).mpr
  nlinarith [mul_pos hr hs.1]


theorem roundExteriorCoordinate_norm {z : RoundCylinderSpace}
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) :
    ‖roundExteriorCoordinate r z‖ = r / (1 - z.2) := by
  simp only [roundExteriorCoordinate, norm_smul, Real.norm_eq_abs,
    abs_of_pos (hr.trans (roundExterior_radius_gt hr hz.2)),
    show ‖z.1.val‖ = 1 by simp, mul_one]


theorem roundExteriorCoordinate_mem {z : RoundCylinderSpace}
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) :
    r < ‖roundExteriorCoordinate r z‖ := by
  rw [roundExteriorCoordinate_norm hr hz]
  exact roundExterior_radius_gt hr hz.2


theorem roundExteriorInverse_mem {x : StandardCapSpace} (hx : r < ‖x‖) :
    roundExteriorInverse r x ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) 1 := by
  have hnorm : 0 < ‖x‖ := hr.trans hx
  refine ⟨Set.mem_univ _, ?_, ?_⟩
  · change 0 < 1 - r / ‖x‖
    exact sub_pos.mpr ((div_lt_one hnorm).mpr hx)
  · change 1 - r / ‖x‖ < 1
    linarith [div_pos hr hnorm]


theorem roundExterior_left_inverse :
    Set.LeftInvOn (roundExteriorInverse r) (roundExteriorCoordinate r)
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) := by
  intro z hz
  apply Prod.ext
  · exact capUnitDirection_smul z.1 (hr.trans (roundExterior_radius_gt hr hz.2))
  · change 1 - r / ‖roundExteriorCoordinate r z‖ = z.2
    rw [roundExteriorCoordinate_norm hr hz]
    field_simp [hr.ne', (sub_pos.mpr hz.2.2).ne'] <;> ring


theorem roundExterior_right_inverse :
    Set.LeftInvOn (roundExteriorCoordinate r) (roundExteriorInverse r) {x | r < ‖x‖} := by
  intro x hx
  have hnorm : 0 < ‖x‖ := hr.trans hx
  change (r / (1 - (1 - r / ‖x‖))) • (capUnitDirection x).val = x
  rw [sub_sub_cancel]
  have heq : r / (r / ‖x‖) = ‖x‖ := by field_simp [hr.ne', hnorm.ne']
  rw [heq, capUnitDirection_radial]


theorem roundExteriorCoordinate_image :
    roundExteriorCoordinate r '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) = {x | r < ‖x‖} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact roundExteriorCoordinate_mem hr hz
  · intro x hx
    exact ⟨roundExteriorInverse r x, roundExteriorInverse_mem hr hx,
      roundExterior_right_inverse hr hx⟩

omit hr in

theorem roundExteriorCoordinate_smooth :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (roundExteriorCoordinate r)
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) := by
  let : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) := ⟨by simp [StandardCapSpace]⟩
  have hrad : ContDiffOn ℝ ∞ (fun s : ℝ => r / (1 - s)) (Set.Ioo (0 : ℝ) 1) := by
    intro s hs
    exact (contDiffAt_const.div (contDiffAt_const.sub contDiffAt_id)
      (sub_pos.mpr hs.2).ne').contDiffWithinAt
  have hrad' : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : RoundCylinderSpace => r / (1 - z.2)) (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) :=
    hrad.contMDiffOn.comp contMDiff_snd.contMDiffOn (fun _ hz => hz.2)
  exact hrad'.smul (contMDiff_coe_sphere.comp contMDiff_fst).contMDiffOn


theorem roundExteriorInverse_smooth :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (roundExteriorInverse r) {x | r < ‖x‖} := by
  apply (capUnitDirection_smooth.mono (fun x hx => norm_pos_iff.mp (hr.trans hx))).prodMk
  intro x hx
  have hnorm : 0 < ‖x‖ := hr.trans hx
  have hs : ContDiffAt ℝ ∞ (fun y : StandardCapSpace => 1 - r / ‖y‖) x :=
    contDiffAt_const.sub (contDiffAt_const.div
      (contDiffAt_norm ℝ (norm_pos_iff.mp hnorm)) hnorm.ne')
  exact hs.contMDiffAt.contMDiffWithinAt


noncomputable def roundExteriorHomeomorph :
    (UnitTwoSphere × Set.Ioo (0 : ℝ) 1) ≃ₜ {x : StandardCapSpace | r < ‖x‖} where
  toFun z := ⟨roundExteriorCoordinate r (z.1, z.2.val),
    roundExteriorCoordinate_mem hr ⟨Set.mem_univ _, z.2.property⟩⟩
  invFun x := ((roundExteriorInverse r x.val).1,
    ⟨(roundExteriorInverse r x.val).2, (roundExteriorInverse_mem hr x.property).2⟩)
  left_inv z := by
    have h := roundExterior_left_inverse hr
      (show (z.1, z.2.val) ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) 1 from
        ⟨Set.mem_univ _, z.2.property⟩)
    apply Prod.ext
    · exact congrArg (fun w : RoundCylinderSpace => w.1) h
    · exact Subtype.ext (congrArg (fun w : RoundCylinderSpace => w.2) h)
  right_inv x := Subtype.ext (roundExterior_right_inverse hr x.property)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (roundExteriorCoordinate_smooth (r := r)).continuousOn.comp_continuous
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (fun z => ⟨Set.mem_univ _, z.2.property⟩)
  continuous_invFun := by
    have h := (roundExteriorInverse_smooth hr).continuousOn.domRestrict
    exact h.fst.prodMk (h.snd.subtype_mk _)


noncomputable def roundExteriorCylinder : OpenCylinderModel {x : StandardCapSpace | r < ‖x‖} where
  homeomorph := roundExteriorHomeomorph hr
  coordinate := roundExteriorCoordinate r
  coordinate_eq _ := rfl
  coordinate_smooth := roundExteriorCoordinate_smooth
  inverse := roundExteriorInverse r
  inverse_mem _ hx := roundExteriorInverse_mem hr hx
  left_inverse := roundExterior_left_inverse hr
  right_inverse := roundExterior_right_inverse hr
  inverse_smooth := roundExteriorInverse_smooth hr


theorem roundExteriorCylinder_radial_coordinate (z : UnitTwoSphere) {R : ℝ} (hR : r < R) :
    (roundExteriorCylinder hr).coordinate (z, 1 - r / R) = R • z.val := by
  have hR0 : 0 < R := hr.trans hR
  change (r / (1 - (1 - r / R))) • z.val = R • z.val
  rw [sub_sub_cancel]
  congr 1
  field_simp [hr.ne', hR0.ne']


theorem roundExteriorCylinder_radial_inverse (z : UnitTwoSphere) {R : ℝ} (hR : r < R) :
    (roundExteriorCylinder hr).inverse (R • z.val) = (z, 1 - r / R) := by
  have hR0 : 0 < R := hr.trans hR
  change (capUnitDirection (R • z.val), 1 - r / ‖R • z.val‖) = (z, 1 - r / R)
  rw [capUnitDirection_smul z hR0, norm_smul, Real.norm_eq_abs, abs_of_pos hR0,
    show ‖z.val‖ = 1 by simp, mul_one]

end PoincareConjecture.M38
