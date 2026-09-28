import PoincareConjecture.Proofs.M38.ForestCutSeparation
import PoincareConjecture.Proofs.M38.SeparatingCut









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38.EventSpanningForest

variable {F : SurgeryFlowData.{u}} {T : ℝ} {hT : T ∈ F.surgery_times}
  [Nonempty (F.slice T).carrier] {P : ∀ i, EventCapCoordinates F T hT i}
  (H : EventSpanningForest F T hT P)


theorem reverse_finset (J : Finset (Fin (F.event T hT).cap_count))
    (hJ : (J : Set (Fin (F.event T hT).cap_count)) ⊆ H.selectedCaps) :
    Relation.ReflTransGen SmoothConnectedSumStep
      (partialCappedCarrier F T hT P Set.univ)
      (partialCappedCarrier F T hT P (J : Set (Fin (F.event T hT).cap_count))ᶜ) := by
  classical
  revert hJ
  refine Finset.induction_on J ?_ ?_
  · intro _
    simp only [Finset.coe_empty, Set.compl_empty]
    exact .refl
  · intro i J hi ih hJ
    have hJ' : (J : Set (Fin (F.event T hT).cap_count)) ⊆ H.selectedCaps :=
      fun j hj => hJ (Finset.mem_insert_of_mem hj)
    have hprev := ih hJ'
    let R : Set (Fin (F.event T hT).cap_count) := (J : Set _)ᶜ
    let S : Set (Fin (F.event T hT).cap_count) := (↑(insert i J) : Set _)ᶜ
    have hiS : i ∉ S := by simp [S]
    have hinsert : insert i S = R := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [R, hi]
      · simp [R, S, hji]
    obtain ⟨e, rfl⟩ := hJ (Finset.mem_insert_self i J)
    have hR : Rᶜ ⊆ H.selectedCaps := by
      simpa only [R, compl_compl] using hJ'
    have hcut : (insert (H.capEdge e) S)ᶜ ⊆ H.selectedCaps := by
      rw [hinsert]
      exact hR
    have hcenters := H.cut_centers_separated e (insert (H.capEdge e) S)
      (Set.mem_insert _ _) hcut
    have hstep := singleCut_separating_step F T hT P S (H.capEdge e) hiS hcenters
    rw [hinsert] at hstep
    exact Relation.ReflTransGen.tail hprev hstep


theorem reverse_selected :
    Relation.ReflTransGen SmoothConnectedSumStep
      (partialCappedCarrier F T hT P Set.univ)
      (partialCappedCarrier F T hT P H.residualCaps) := by
  classical
  have h := H.reverse_finset H.selectedCaps.toFinset (by simp)
  simpa only [Set.coe_toFinset, residualCaps] using h

end PoincareConjecture.M38.EventSpanningForest
