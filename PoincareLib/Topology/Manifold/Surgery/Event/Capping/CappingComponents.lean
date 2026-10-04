import PoincareLib.Topology.Manifold.Surgery.Event.Capping.CappingComponentLabels
import PoincareLib.Topology.Manifold.Surgery.Event.Capping.CappingCarrier
import PoincareLib.Topology.Manifold.Surgery.Event.Components.Components

/-!
# Capping preserves the actual discarded components

The old inclusion induces a homeomorphism on connected-component spaces.
The continuous labels on the quotient are its inverse: every new ball is
connected and meets the old interior in its own nonempty attaching annulus.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

/-- Every point of an attached ball belongs to the component of that
ball's actual old attaching point. -/
theorem cappedCapPatch_component (i : Fin (F.event T hT).cap_count)
    (x : capDoubleBall) :
    ConnectedComponents.mk (eventCappingInclude F T hT P (.inr i) x) =
      ConnectedComponents.mk (cappedOldInclusion F T hT P (P i).attachmentPoint) := by
  let : ConnectedSpace capDoubleBall := capDoubleBall_connected
  have hconnected := isConnected_range
    (eventCappingInclude_openEmbedding F T hT P (.inr i)).continuous
  have hpoint : cappedOldInclusion F T hT P (P i).attachmentPoint =
      eventCappingInclude F T hT P (.inr i) capAnnularPoint := by
    apply cappedOldInclusion_cap F T hT P i capAnnularPoint
    rw [capAnnularPoint_norm]
    norm_num
  apply ConnectedComponents.coe_eq_coe'.mpr
  apply hconnected.subset_connectedComponent ?_ (Set.mem_range_self x)
  rw [hpoint]
  exact Set.mem_range_self _

/-- Component labels invert the map induced by the actual old inclusion.
This includes empty discarded interiors and events with no cap indices.
Source: Proposition 15.3, pp. 357-358, capping the discarded boundary. -/
noncomputable def cappedComponentsHomeomorph :
    ConnectedComponents (eventDiscardedOpen F T hT) ≃ₜ
      ConnectedComponents (CappedDiscardedSpace F T hT P) where
  toFun := (cappedOldInclusion_openEmbedding F T hT P).continuous.connectedComponentsMap
  invFun := (cappedComponentLabel_continuous F T hT P).connectedComponentsLift
  left_inv := by
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    exact cappedComponentLabel_old F T hT P x
  right_inv := by
    intro c
    obtain ⟨q, rfl⟩ := ConnectedComponents.surjective_coe c
    induction q using Quotient.inductionOn with
    | h a =>
        rcases a with ⟨j, x⟩
        cases j with
        | inl y =>
            change ConnectedComponents.mk
              (cappedOldInclusion F T hT P (eventCappingMap F T hT P (.inl y) x)) =
                ConnectedComponents.mk (eventCappingInclude F T hT P (.inl y) x)
            rw [cappedOldInclusion_patch]
        | inr i =>
            exact (cappedCapPatch_component F T hT P i x).symm
  continuous_toFun :=
    (cappedOldInclusion_openEmbedding F T hT P).continuous.connectedComponentsMap_continuous
  continuous_invFun :=
    (cappedComponentLabel_continuous F T hT P).connectedComponentsLift_continuous

/-- The forward map is exactly the class of the actual old inclusion. -/
theorem cappedComponentsHomeomorph_apply (x : eventDiscardedOpen F T hT) :
    cappedComponentsHomeomorph F T hT P (ConnectedComponents.mk x) =
      ConnectedComponents.mk (cappedOldInclusion F T hT P x) := rfl

/-- The inverse is the descended component label of the same quotient point. -/
theorem cappedComponentsHomeomorph_symm_apply (q : CappedDiscardedSpace F T hT P) :
    (cappedComponentsHomeomorph F T hT P).symm (ConnectedComponents.mk q) =
      cappedComponentLabel F T hT P q := rfl

/-- Taking a component in the capped carrier and restricting it to the
old inclusion recovers precisely the original discarded component. -/
theorem cappedOldInclusion_preimage_component (x : eventDiscardedOpen F T hT) :
    cappedOldInclusion F T hT P ⁻¹'
      connectedComponent (cappedOldInclusion F T hT P x) = connectedComponent x := by
  ext y
  constructor
  · intro hy
    apply ConnectedComponents.coe_eq_coe'.mp
    apply (cappedComponentsHomeomorph F T hT P).injective
    exact ConnectedComponents.coe_eq_coe'.mpr hy
  · intro hy
    apply ConnectedComponents.coe_eq_coe'.mp
    exact congrArg (cappedComponentsHomeomorph F T hT P)
      (ConnectedComponents.coe_eq_coe'.mpr hy)

include P in
/-- The actual discarded interior has finitely many components because
its capped carrier is compact and locally connected. -/
theorem eventDiscardedOpen_finite_components :
    Finite (ConnectedComponents (eventDiscardedOpen F T hT)) := by
  let : Finite (ConnectedComponents (CappedDiscardedSpace F T hT P)) :=
    finite_components (cappedDiscardedCarrier F T hT P)
      (cappedDiscardedCarrier_compact F T hT P)
  exact Finite.of_injective (cappedComponentsHomeomorph F T hT P)
    (cappedComponentsHomeomorph F T hT P).injective

end PoincareMT.M38
