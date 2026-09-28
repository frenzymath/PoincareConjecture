import PoincareConjecture.Proofs.M38.PartialCutCompact








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S : Set (Fin (F.event T hT).cap_count))

noncomputable local instance partialBallChartedSpace :
    ChartedSpace StandardCapSpace (PartialCappedSpace F T hT P S) :=
  partialCappedChartedSpace F T hT P S

local instance partialBallIsManifold : IsManifold (𝓡 3) ∞ (PartialCappedSpace F T hT P S) :=
  partialCappedSpace_isManifold F T hT P S


noncomputable def partialCappingChart (j : PartialCappingIndex F T hT P S) :
    OpenPartialHomeomorph (PartialCappedSpace F T hT P S) StandardCapSpace :=
  Poincare.Gluing.quotientChart
    (fun j => (partialCappingDomain F T hT P S j : Set StandardCapSpace))
    (fun j => (partialCappingDomain F T hT P S j).isOpen) (partialCappingOverlap F T hT P S) j


theorem partialCappingChart_target (j : PartialCappingIndex F T hT P S) :
    (partialCappingChart F T hT P S j).target = partialCappingDomain F T hT P S j :=
  Poincare.Gluing.quotientChart_target _ _ _ j


theorem partialCappingChart_source (j : PartialCappingIndex F T hT P S) :
    (partialCappingChart F T hT P S j).source =
      Set.range (partialCappingInclude F T hT P S j) := by
  rw [partialCappingChart, Poincare.Gluing.quotientChart_source, Set.image_univ]
  rfl


theorem partialCappingChart_symm (j : PartialCappingIndex F T hT P S)
    (x : partialCappingDomain F T hT P S j) :
    (partialCappingChart F T hT P S j).symm x.val = partialCappingInclude F T hT P S j x :=
  Poincare.Gluing.quotientChart_symm_apply _ _ _ j x.property


noncomputable def partialCapBall (a : S × Bool) :
    SurgeryBallEmbedding (partialCappedCarrier F T hT P S) := by
  let e := partialCappingChart F T hT P S (.inr a)
  have he : e ∈ IsManifold.maximalAtlas (𝓡 3) ∞ (PartialCappedSpace F T hT P S) :=
    IsManifold.subset_maximalAtlas ⟨Sum.inr a, rfl⟩
  have ht : e.target = Metric.ball 0 2 := partialCappingChart_target F T hT P S (.inr a)
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
        partialCappingInclude F T hT P S (.inr a) :=
      funext (partialCappingChart_symm F T hT P S (.inr a))
    rw [heq]
    exact partialCappingInclude_openEmbedding F T hT P S (.inr a)


theorem partialCapBall_map (a : S × Bool) (x : capDoubleBall) :
    (partialCapBall F T hT P S a).map x.val = partialCappingInclude F T hT P S (.inr a) x :=
  partialCappingChart_symm F T hT P S (.inr a) x


theorem partialCapBall_closedBall (a : S × Bool) :
    (partialCapBall F T hT P S a).closedBall = partialCappingInclude F T hT P S (.inr a) ''
      {x : capDoubleBall | ‖x.val‖ ≤ 1} := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hnorm : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    let z : capDoubleBall := ⟨x, by
      change dist x 0 < 2
      rw [dist_zero_right]
      linarith⟩
    exact ⟨z, hnorm, (partialCapBall_map F T hT P S a z).symm⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.val, ?_, partialCapBall_map F T hT P S a x⟩
    change ‖x.val‖ ≤ (1 : ℝ) at hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx


theorem partialCapBall_attachment (a : S × Bool) (x : capDoubleBall) (hx : 1 < ‖x.val‖) :
    (partialCapBall F T hT P S a).map x.val =
      partialOldInclusion F T hT P S (cutAttachmentChart F T hT P S a x) := by
  rw [partialCapBall_map]
  exact (partialOldInclusion_cap F T hT P S a x hx).symm

end PoincareConjecture.M38
