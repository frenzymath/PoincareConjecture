import PoincareLib.Topology.Manifold.Surgery.Event.Cap.CapAnnulus

/-!
# Annular coordinates on both sides of actual surgery cuts

Reflection of the longitudinal coordinate gives the retained-side
attachment. Both sides use the same actual collar and its inverse.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

/-- The positive side keeps the collar coordinate; the negative side
reverses it. No angular coordinate is changed. -/
noncomputable def cutSideReflection (positive : Bool) :
    Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      RoundCylinderSpace RoundCylinderSpace ∞ where
  toFun := fun z => (z.1, if positive then z.2 else -z.2)
  invFun := fun z => (z.1, if positive then z.2 else -z.2)
  left_inv := by intro z; cases positive <;> simp
  right_inv := by intro z; cases positive <;> simp
  contMDiff_toFun := by
    cases positive
    · exact contMDiff_fst.prodMk contMDiff_snd.neg
    · exact contMDiff_id
  contMDiff_invFun := by
    cases positive
    · exact contMDiff_fst.prodMk contMDiff_snd.neg
    · exact contMDiff_id

/-- The chosen diffeomorphism has the displayed literal point map. -/
@[simp] theorem cutSideReflection_apply (positive : Bool) (z : RoundCylinderSpace) :
    cutSideReflection positive z = (z.1, if positive then z.2 else -z.2) := rfl

/-- The same reflection is its inverse. -/
@[simp] theorem cutSideReflection_self (positive : Bool) (z : RoundCylinderSpace) :
    cutSideReflection positive (cutSideReflection positive z) = z := by
  cases positive <;> simp only [cutSideReflection_apply, Bool.false_eq_true,
    ↓reduceIte, neg_neg, Prod.mk.eta]

/-- Both choices fix the literal central sphere pointwise. -/
@[simp] theorem cutSideReflection_zero (positive : Bool) (z : UnitTwoSphere) :
    cutSideReflection positive (z, 0) = (z, 0) := by
  cases positive <;> simp only [cutSideReflection_apply, Bool.false_eq_true,
    ↓reduceIte, neg_zero]

/-- Reflection preserves precisely the full open collar domain. -/
theorem cutSideReflection_mem_full (positive : Bool) (z : RoundCylinderSpace) :
    cutSideReflection positive z ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 ↔
      z ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 := by
  cases positive <;> simp only [cutSideReflection_apply, Bool.false_eq_true,
    ↓reduceIte, Set.mem_prod, Set.mem_univ, true_and, Set.mem_Ioo]
  · constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- The two reflected positive halves are disjoint. -/
theorem cutSideReflection_halves_disjoint :
    Disjoint (cutSideReflection false '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1))
      (cutSideReflection true '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, heq⟩
  have h := congrArg Prod.snd heq
  change w.2 = -z.2 at h
  linarith [hz.2.1, hw.2.1]

namespace EventCapCoordinates

variable {F : SurgeryFlowData.{u}} {T : ℝ} {hT : T ∈ F.surgery_times}
  [Nonempty (F.slice T).carrier] {i : Fin (F.event T hT).cap_count}
  (P : EventCapCoordinates F T hT i)

/-- The annular map attaches to the indicated side of this actual cut. -/
theorem cutAnnular_map_smooth (positive : Bool) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (P.collar ∘ cutSideReflection positive ∘ capAttachCoordinates)
      {x : StandardCapSpace | 1 < ‖x‖ ∧ ‖x‖ < 2} := by
  apply (event_cap_collar_smooth F T hT i P.width_pos P.width_lt P.shell_domain).comp
    ((cutSideReflection positive).contMDiff.comp_contMDiffOn
      (capAttachCoordinates_smooth.mono ?_)) ?_
  · intro x hx
    exact norm_pos_iff.mp (zero_lt_one.trans hx.1)
  · intro x hx
    exact (cutSideReflection_mem_full positive _).mpr
      (positive_collar_subset (capAttachCoordinates_mem hx))

/-- The inverse uses the same longitudinal reflection and actual collar inverse. -/
theorem cutAnnular_inverse_smooth (positive : Bool) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (capAttachVector ∘ cutSideReflection positive ∘ P.collarInverse)
      ((P.collar ∘ cutSideReflection positive) ''
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1)) := by
  apply capAttachVector_smooth.comp_contMDiffOn
    ((cutSideReflection positive).contMDiff.comp_contMDiffOn
      ((event_cap_collar_inverse_smooth F T hT i P.width_pos P.width_lt
        P.shell_domain).mono ?_))
  rintro _ ⟨z, hz, rfl⟩
  exact Set.mem_image_of_mem P.collar
    ((cutSideReflection_mem_full positive z).mpr (positive_collar_subset hz))

/-- The unit-to-double annulus is smoothly identified with exactly one
half of the actual collar, for either sign. -/
noncomputable def cutAnnularChart (positive : Bool) :
    OpenPartialHomeomorph StandardCapSpace (F.slice (F.event T hT).tMinus).carrier where
  toFun := P.collar ∘ cutSideReflection positive ∘ capAttachCoordinates
  invFun := capAttachVector ∘ cutSideReflection positive ∘ P.collarInverse
  source := {x | 1 < ‖x‖ ∧ ‖x‖ < 2}
  target := (P.collar ∘ cutSideReflection positive) '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1)
  map_source' := fun x hx => Set.mem_image_of_mem _ (capAttachCoordinates_mem hx)
  map_target' := by
    rintro _ ⟨z, hz, rfl⟩
    have hfull := (cutSideReflection_mem_full positive z).mpr (positive_collar_subset hz)
    have hinv := P.collarChart.left_inv hfull
    change P.collarInverse (P.collar (cutSideReflection positive z)) = _ at hinv
    simp only [Function.comp_apply, hinv, cutSideReflection_self]
    exact capAttachVector_mem hz
  left_inv' := by
    intro x hx
    have hfull := (cutSideReflection_mem_full positive _).mpr
      (positive_collar_subset (capAttachCoordinates_mem hx))
    have hinv := P.collarChart.left_inv hfull
    change P.collarInverse (P.collar (cutSideReflection positive (capAttachCoordinates x))) = _
      at hinv
    simp only [Function.comp_apply, hinv, cutSideReflection_self, capAttachVector_coordinates]
  right_inv' := by
    rintro _ ⟨z, hz, rfl⟩
    have hfull := (cutSideReflection_mem_full positive z).mpr (positive_collar_subset hz)
    have hinv := P.collarChart.left_inv hfull
    change P.collarInverse (P.collar (cutSideReflection positive z)) = _ at hinv
    simp only [Function.comp_apply, hinv, cutSideReflection_self,
      capAttachCoordinates_vector hz]
  continuousOn_toFun := P.cutAnnular_map_smooth positive |>.continuousOn
  continuousOn_invFun := P.cutAnnular_inverse_smooth positive |>.continuousOn
  open_source := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  open_target := by
    rw [Set.image_comp]
    apply P.collar_open_on
      ((cutSideReflection positive).toHomeomorph.isOpenMap _ (isOpen_univ.prod isOpen_Ioo))
    rintro _ ⟨z, hz, rfl⟩
    exact (cutSideReflection_mem_full positive z).mpr (positive_collar_subset hz)

/-- Every attaching target stays inside its actual full collar. -/
theorem cutAnnularChart_target_subset (positive : Bool) :
    (P.cutAnnularChart positive).target ⊆
      P.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) := by
  rintro _ ⟨z, hz, rfl⟩
  exact Set.mem_image_of_mem P.collar
    ((cutSideReflection_mem_full positive z).mpr (positive_collar_subset hz))

/-- Neither side's attaching annulus meets its own removed central sphere. -/
theorem cutAnnularChart_central_disjoint (positive : Bool) :
    Disjoint (P.cutAnnularChart positive).target
      (P.collar '' (Set.univ ×ˢ ({0} : Set ℝ))) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨z, hz, rfl⟩ ⟨⟨w, s⟩, ⟨_, hs⟩, heq⟩
  have hs0 : s = 0 := hs
  subst s
  have he := P.collarChart.injOn
    (show (w, 0) ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 by simp)
    ((cutSideReflection_mem_full positive z).mpr (positive_collar_subset hz)) heq
  have h := congrArg Prod.snd he
  cases positive <;> simp only [cutSideReflection_apply, Bool.false_eq_true,
    ↓reduceIte] at h <;> linarith [hz.2.1]

/-- The attaching annuli on the two sides of this same cut are disjoint. -/
theorem cutAnnularChart_opposite_disjoint :
    Disjoint (P.cutAnnularChart false).target (P.cutAnnularChart true).target := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, heq⟩
  have he := P.collarChart.injOn
    ((cutSideReflection_mem_full true w).mpr (positive_collar_subset hw))
    ((cutSideReflection_mem_full false z).mpr (positive_collar_subset hz)) heq
  exact Set.disjoint_left.mp cutSideReflection_halves_disjoint
    (Set.mem_image_of_mem _ hz) ⟨w, hw, he⟩

end EventCapCoordinates

end PoincareMT.M38
