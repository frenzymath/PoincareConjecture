import PoincareConjecture.Proofs.M38.EventCapCoordinates









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M38


noncomputable def capAttachVector (z : RoundCylinderSpace) : StandardCapSpace :=
  (1 + z.2) • z.1.val


theorem capAttachVector_smooth :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ capAttachVector := by
  let : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) := ⟨by simp [StandardCapSpace]⟩
  have hrad : ContDiff ℝ ∞ (fun s : ℝ => 1 + s) := contDiff_const.add contDiff_id
  have hcoe : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun z : UnitTwoSphere => z.val) :=
    contMDiff_coe_sphere
  exact (hrad.contMDiff.comp contMDiff_snd).smul (hcoe.comp contMDiff_fst)


theorem capAttachVector_coordinates (x : StandardCapSpace) :
    capAttachVector (capAttachCoordinates x) = x := by
  change (1 + (‖x‖ - 1)) • (capUnitDirection x).val = x
  rw [show 1 + (‖x‖ - 1) = ‖x‖ by ring, capUnitDirection_radial]


theorem capAttachCoordinates_vector {z : RoundCylinderSpace}
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) :
    capAttachCoordinates (capAttachVector z) = z := by
  have hpos : 0 < 1 + z.2 := by linarith [hz.2.1]
  apply Prod.ext
  · exact capUnitDirection_smul z.1 hpos
  · change ‖(1 + z.2) • z.1.val‖ - 1 = z.2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos,
      show ‖z.1.val‖ = 1 by simp, mul_one]
    ring


theorem capAttachCoordinates_mem {x : StandardCapSpace} (hx : 1 < ‖x‖ ∧ ‖x‖ < 2) :
    capAttachCoordinates x ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) 1 := by
  refine ⟨Set.mem_univ _, ?_, ?_⟩ <;> dsimp [capAttachCoordinates] <;> linarith [hx.1, hx.2]


theorem capAttachVector_mem {z : RoundCylinderSpace}
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) :
    1 < ‖capAttachVector z‖ ∧ ‖capAttachVector z‖ < 2 := by
  have hpos : 0 < 1 + z.2 := by linarith [hz.2.1]
  simp only [capAttachVector, norm_smul, Real.norm_eq_abs, abs_of_pos hpos,
    show ‖z.1.val‖ = 1 by simp, mul_one]
  constructor <;> linarith [hz.2.1, hz.2.2]


theorem positive_collar_subset :
    (Set.univ : Set UnitTwoSphere) ×ˢ Set.Ioo (0 : ℝ) 1 ⊆
      Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 :=
  fun _ hz => ⟨hz.1, neg_one_lt_zero.trans hz.2.1, hz.2.2⟩

namespace EventCapCoordinates

variable {F : SurgeryFlowData.{u}} {T : ℝ} {hT : T ∈ F.surgery_times}
  [Nonempty (F.slice T).carrier] {i : Fin (F.event T hT).cap_count}
  (P : EventCapCoordinates F T hT i)


theorem annular_map_smooth :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (P.collar ∘ capAttachCoordinates)
      {x : StandardCapSpace | 1 < ‖x‖ ∧ ‖x‖ < 2} := by
  apply (event_cap_collar_smooth F T hT i P.width_pos P.width_lt P.shell_domain).comp
    (capAttachCoordinates_smooth.mono ?_) ?_
  · intro x hx
    exact norm_pos_iff.mp (zero_lt_one.trans hx.1)
  · exact fun x hx => positive_collar_subset (capAttachCoordinates_mem hx)


theorem annular_inverse_smooth :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (capAttachVector ∘ P.collarInverse)
      (P.collar '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1)) :=
  capAttachVector_smooth.comp_contMDiffOn
    ((event_cap_collar_inverse_smooth F T hT i P.width_pos P.width_lt P.shell_domain).mono
      (Set.image_mono positive_collar_subset))


noncomputable def annularChart :
    OpenPartialHomeomorph StandardCapSpace (F.slice (F.event T hT).tMinus).carrier where
  toFun := P.collar ∘ capAttachCoordinates
  invFun := capAttachVector ∘ P.collarInverse
  source := {x | 1 < ‖x‖ ∧ ‖x‖ < 2}
  target := P.collar '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1)
  map_source' := fun x hx => Set.mem_image_of_mem P.collar (capAttachCoordinates_mem hx)
  map_target' := by
    rintro y ⟨z, hz, rfl⟩
    change 1 < ‖capAttachVector (P.collarInverse (P.collar z))‖ ∧
      ‖capAttachVector (P.collarInverse (P.collar z))‖ < 2
    have hinv : P.collarInverse (P.collar z) = z := P.collarChart.left_inv (positive_collar_subset hz)
    rw [hinv]
    exact capAttachVector_mem hz
  left_inv' := by
    intro x hx
    change capAttachVector (P.collarInverse (P.collar (capAttachCoordinates x))) = x
    have hinv : P.collarInverse (P.collar (capAttachCoordinates x)) = capAttachCoordinates x :=
      P.collarChart.left_inv (positive_collar_subset (capAttachCoordinates_mem hx))
    rw [hinv, capAttachVector_coordinates]
  right_inv' := by
    rintro y ⟨z, hz, rfl⟩
    change P.collar (capAttachCoordinates (capAttachVector (P.collarInverse (P.collar z)))) =
      P.collar z
    have hinv : P.collarInverse (P.collar z) = z := P.collarChart.left_inv (positive_collar_subset hz)
    rw [hinv, capAttachCoordinates_vector hz]
  continuousOn_toFun := P.annular_map_smooth.continuousOn
  continuousOn_invFun := P.annular_inverse_smooth.continuousOn
  open_source := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  open_target := P.collar_open_on (isOpen_univ.prod isOpen_Ioo) positive_collar_subset


theorem annular_target_discarded :
    P.annularChart.target ⊆ (F.event T hT).retained_preᶜ :=
  fun _ hx => Set.disjoint_left.mp P.positive_disjoint hx

end EventCapCoordinates

end PoincareConjecture.M38
