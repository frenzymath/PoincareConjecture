import PoincareLib.Topology.Manifold.Surgery.Event.Event.EventGraphCover

/-!
# Actual incidence components and original pre-surgery components

The continuous graph label and the inclusion-induced pre-component map
are inverse on the actual quotient representatives. Thus the graph's
components are precisely the original pre-surgery components.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

/-- The glued graph label recovers the actual pre-component at every point. -/
theorem eventGraphPreComponent_label (x : (F.slice (F.event T hT).tMinus).carrier) :
    eventGraphPreComponent F T hT P (preEventGraphLabel F T hT P x) =
      ConnectedComponents.mk x := by
  obtain ⟨j, hj⟩ := eventPrePatch_cover F T hT P x
  have hx : x ∈ eventPrePatch F T hT P j := mem_of_mem_nhds hj
  rw [preEventGraphLabel_patch F T hT P j ⟨x, hx⟩]
  cases j with
  | inl b => cases b <;> rfl
  | inr i => exact ((P i).full_collar_pre_component x hx).symm

/-- The graph label descends along the actual pre-slice component quotient. -/
noncomputable def preEventGraphComponent :
    ConnectedComponents (F.slice (F.event T hT).tMinus).carrier → EventGraphComponent F T hT P :=
  (preEventGraphLabel F T hT P).continuous.connectedComponentsLift

/-- The descended map keeps the original continuous label on representatives. -/
theorem preEventGraphComponent_apply (x : (F.slice (F.event T hT).tMinus).carrier) :
    preEventGraphComponent F T hT P (ConnectedComponents.mk x) =
      preEventGraphLabel F T hT P x := rfl

/-- Graph connected components identify exactly with the components of the
actual pre-surgery slice. Source: Proposition 15.3, pp. 357-358, the finite
cutting system. All original cap edges remain in eventIncidenceGraph. -/
noncomputable def eventGraphComponentsHomeomorph :
    EventGraphComponent F T hT P ≃ₜ
      ConnectedComponents (F.slice (F.event T hT).tMinus).carrier where
  toFun := eventGraphPreComponent F T hT P
  invFun := preEventGraphComponent F T hT P
  left_inv := by
    intro c
    refine SimpleGraph.ConnectedComponent.ind (fun v => ?_) c
    cases v with
    | inl v =>
        obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe v
        exact preEventGraphLabel_retained F T hT P x
    | inr v =>
        obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe v
        exact preEventGraphLabel_discarded F T hT P x
  right_inv := by
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    exact eventGraphPreComponent_label F T hT P x
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := (preEventGraphLabel F T hT P).continuous.connectedComponentsLift_continuous

/-- The forward correspondence is the literal inclusion-induced vertex label. -/
theorem eventGraphComponentsHomeomorph_vertex (v : EventCutVertex F T hT) :
    eventGraphComponentsHomeomorph F T hT P (eventGraphVertexClass F T hT P v) =
      eventVertexPreComponent F T hT v := rfl

/-- The inverse uses the exact continuous label on the actual pre-slice. -/
theorem eventGraphComponentsHomeomorph_symm_apply
    (x : (F.slice (F.event T hT).tMinus).carrier) :
    (eventGraphComponentsHomeomorph F T hT P).symm (ConnectedComponents.mk x) =
      preEventGraphLabel F T hT P x := rfl

/-- Two actual cut vertices are joined by a graph walk exactly when their
open regions lie in the same original pre-slice component. -/
theorem eventIncidence_reachable_iff (x y : EventCutVertex F T hT) :
    (eventIncidenceAdjacency F T hT P).Reachable x y ↔
      eventVertexPreComponent F T hT x = eventVertexPreComponent F T hT y := by
  rw [← SimpleGraph.ConnectedComponent.eq]
  exact (eventGraphComponentsHomeomorph F T hT P).injective.eq_iff.symm

/-- The graph-component set is finite, including any isolated whole components. -/
theorem eventGraphComponent_finite : Finite (EventGraphComponent F T hT P) := by
  let : Finite (EventCutVertex F T hT) := eventCutVertex_finite F T hT P
  exact inferInstanceAs (Finite (eventIncidenceAdjacency F T hT P).ConnectedComponent)

end PoincareMT.M38
