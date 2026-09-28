import PoincareConjecture.Proofs.M38.CappingCarrier









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

noncomputable local instance cappedBallChartedSpace :
    ChartedSpace StandardCapSpace (CappedDiscardedSpace F T hT P) :=
  cappedDiscardedChartedSpace F T hT P

local instance cappedBallIsManifold : IsManifold (𝓡 3) ∞ (CappedDiscardedSpace F T hT P) :=
  cappedDiscardedSpace_isManifold F T hT P


noncomputable def eventCappingChart (j : EventCappingIndex F T hT) :
    OpenPartialHomeomorph (CappedDiscardedSpace F T hT P) StandardCapSpace :=
  Poincare.Gluing.quotientChart
    (fun j => (eventCappingDomain F T hT j : Set StandardCapSpace))
    (fun j => (eventCappingDomain F T hT j).isOpen) (eventCappingOverlap F T hT P) j


theorem eventCappingChart_target (j : EventCappingIndex F T hT) :
    (eventCappingChart F T hT P j).target = eventCappingDomain F T hT j :=
  Poincare.Gluing.quotientChart_target _ _ _ j


theorem eventCappingChart_source (j : EventCappingIndex F T hT) :
    (eventCappingChart F T hT P j).source = Set.range (eventCappingInclude F T hT P j) := by
  rw [eventCappingChart, Poincare.Gluing.quotientChart_source, Set.image_univ]
  rfl


theorem eventCappingChart_symm (j : EventCappingIndex F T hT)
    (x : eventCappingDomain F T hT j) :
    (eventCappingChart F T hT P j).symm x.val = eventCappingInclude F T hT P j x :=
  Poincare.Gluing.quotientChart_symm_apply _ _ _ j x.property


noncomputable def cappedCapBall (i : Fin (F.event T hT).cap_count) :
    SurgeryBallEmbedding (cappedDiscardedCarrier F T hT P) := by
  let e := eventCappingChart F T hT P (.inr i)
  have he : e ∈ IsManifold.maximalAtlas (𝓡 3) ∞ (CappedDiscardedSpace F T hT P) :=
    IsManifold.subset_maximalAtlas ⟨Sum.inr i, rfl⟩
  have ht : e.target = Metric.ball 0 2 := eventCappingChart_target F T hT P (.inr i)
  have hs : e.symm '' Metric.ball 0 2 = e.source := by
    rw [← ht]
    exact e.symm.image_source_eq_target
  refine {
    map := e.symm
    inverse := e
    map_smooth := ?_
    inverse_smooth := ?_
    left_inverse := ?_
    right_inverse := ?_
    open_embedding := ?_ }
  · rw [← ht]
    exact contMDiffOn_symm_of_mem_maximalAtlas he
  · rw [hs]
    exact contMDiffOn_of_mem_maximalAtlas he
  · intro x hx
    exact e.right_inv (ht.symm ▸ hx)
  · intro q hq
    exact e.left_inv (hs ▸ hq)
  · have heq : (fun x : Metric.ball (0 : StandardCapSpace) 2 => e.symm x.val) =
        eventCappingInclude F T hT P (.inr i) :=
      funext (eventCappingChart_symm F T hT P (.inr i))
    rw [heq]
    exact eventCappingInclude_openEmbedding F T hT P (.inr i)


theorem cappedCapBall_map (i : Fin (F.event T hT).cap_count) (x : capDoubleBall) :
    (cappedCapBall F T hT P i).map x.val = eventCappingInclude F T hT P (.inr i) x :=
  eventCappingChart_symm F T hT P (.inr i) x


theorem cappedCapBall_closedBall (i : Fin (F.event T hT).cap_count) :
    (cappedCapBall F T hT P i).closedBall = eventCappingInclude F T hT P (.inr i) ''
      {x : capDoubleBall | ‖x.val‖ ≤ 1} := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hnorm : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    let z : capDoubleBall := ⟨x, by
      change dist x 0 < 2
      rw [dist_zero_right]
      linarith⟩
    exact ⟨z, hnorm, (cappedCapBall_map F T hT P i z).symm⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.val, ?_, cappedCapBall_map F T hT P i x⟩
    change ‖x.val‖ ≤ (1 : ℝ) at hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx



theorem cappedCapBall_attachment (i : Fin (F.event T hT).cap_count)
    (x : capDoubleBall) (hx : 1 < ‖x.val‖) :
    (cappedCapBall F T hT P i).map x.val =
      cappedOldInclusion F T hT P ((P i).attachmentChart x) := by
  rw [cappedCapBall_map]
  exact (cappedOldInclusion_cap F T hT P i x hx).symm

end PoincareConjecture.M38
