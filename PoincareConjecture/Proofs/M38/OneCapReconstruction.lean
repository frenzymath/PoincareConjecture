import PoincareConjecture.Proofs.M38.DiscardedIdentification
import PoincareConjecture.Proofs.M38.RetentionInterior










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)



noncomputable def oneCapConnectedSumData (i : Fin (F.event T hT).cap_count)
    (hall : ∀ j, j = i) :
    SmoothConnectedSumData (F.slice T) (cappedDiscardedCarrier F T hT P)
      (F.slice (F.event T hT).tMinus) := by
  letI : Nonempty (Fin (F.event T hT).cap_count) := ⟨i⟩
  have hfirst : (P i).ball.closedBall = ⋃ j, ((F.event T hT).caps j).carrier := by
    rw [(P i).ball_closedBall]
    exact (Set.iUnion_eq_const fun j => congrArg
      (fun k => ((F.event T hT).caps k).carrier) (hall j)).symm
  have hsecond : (cappedCapBall F T hT P i).closedBall =
      ⋃ j, (cappedCapBall F T hT P j).closedBall :=
    (Set.iUnion_eq_const fun j => congrArg
      (fun k => (cappedCapBall F T hT P k).closedBall) (hall j)).symm
  have hcentral : (P i).collar '' (Set.univ ×ˢ ({0} : Set ℝ)) =
      frontier (F.event T hT).retained_pre := by
    rw [(P i).collar_central, (F.event T hT).pre_boundary]
    exact (Set.iUnion_eq_const fun j => congrArg
      (fun k => (F.event T hT).limit_identify.inverse ''
        ((F.event T hT).necks k).neck.central_sphere) (hall j)).symm
  let e₁ := retentionInteriorInverseEquivalence F T hT
  let e₂ := cappedDiscardedRegionEquivalence F T hT P i
  refine {
    first_ball := (P i).ball
    second_ball := cappedCapBall F T hT P i
    first_region := interior (F.event T hT).retained_pre
    second_region := (F.event T hT).retained_preᶜ
    first_open := isOpen_interior
    second_open := (F.event T hT).retained_pre_compact.isClosed.isOpen_compl
    first_identify := {
      map := e₁.map
      inverse := e₁.inverse
      map_image := by rw [hfirst]; exact e₁.map_image
      inverse_image := by rw [hfirst]; exact e₁.inverse_image
      left_inverse := by rw [hfirst]; exact e₁.left_inverse
      right_inverse := e₁.right_inverse
      map_smooth := by rw [hfirst]; exact e₁.map_smooth
      inverse_smooth := e₁.inverse_smooth }
    second_identify := {
      map := e₂.map
      inverse := e₂.inverse
      map_image := by rw [hsecond]; exact e₂.map_image
      inverse_image := by rw [hsecond]; exact e₂.inverse_image
      left_inverse := by rw [hsecond]; exact e₂.left_inverse
      right_inverse := e₂.right_inverse
      map_smooth := by rw [hsecond]; exact e₂.map_smooth
      inverse_smooth := e₂.inverse_smooth }
    regions_disjoint := Set.disjoint_left.mpr (fun _ hx hy => hy (interior_subset hx))
    sphere_gluing := Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞
    collar := (P i).collar
    collar_inverse := (P i).collarInverse
    collar_smooth := event_cap_collar_smooth F T hT i (P i).width_pos
      (P i).width_lt (P i).shell_domain
    collar_inverse_smooth := event_cap_collar_inverse_smooth F T hT i (P i).width_pos
      (P i).width_lt (P i).shell_domain
    collar_left_inverse := fun _ hx => (P i).collarChart.left_inv hx
    collar_right_inverse := fun _ hx => (P i).collarChart.right_inv hx
    collar_open := (P i).collarChart.open_target
    negative_gluing := (P i).negative_gluing
    positive_gluing := cappedDiscardedRegionEquivalence_positive F T hT P i
    central_disjoint := ?_
    cover := ?_ }
  · rw [hcentral, (F.event T hT).retained_pre_compact.isClosed.frontier_eq]
    exact Set.disjoint_left.mpr (fun _ hx hy => hy.elim hx.2 (fun h => h hx.1))
  · rw [hcentral, (F.event T hT).retained_pre_compact.isClosed.frontier_eq]
    apply Set.eq_univ_of_forall
    intro x
    by_cases hr : x ∈ (F.event T hT).retained_pre
    · by_cases hi : x ∈ interior (F.event T hT).retained_pre
      · exact Or.inl (Or.inl hi)
      · exact Or.inr ⟨hr, hi⟩
    · exact Or.inl (Or.inr hr)



theorem exists_one_cap_reconstruction (hcount : (F.event T hT).cap_count = 1) :
    ∃ B : GeneralizedSliceCarrier.{u}, IsCompact (Set.univ : Set B.carrier) ∧
      Nonempty (SmoothConnectedSumData (F.slice T) B (F.slice (F.event T hT).tMinus)) := by
  classical
  let P' : ∀ j, EventCapCoordinates F T hT j :=
    fun j => Classical.choice (exists_event_cap_coordinates F T hT j)
  let i : Fin (F.event T hT).cap_count := ⟨0, by omega⟩
  have hall (j : Fin (F.event T hT).cap_count) : j = i := by
    apply Fin.ext
    have hj := j.isLt
    change j.val = 0
    omega
  exact ⟨cappedDiscardedCarrier F T hT P', cappedDiscardedCarrier_compact F T hT P',
    ⟨oneCapConnectedSumData F T hT P' i hall⟩⟩

end PoincareConjecture.M38
