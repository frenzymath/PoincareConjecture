import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.Path
import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.Transport.Comparison.ComponentGeometry
import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.Transport.Comparison.NeckSphereEmbedding
import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.Transport.Comparison.RetainedRegion

/-!
# Comparison input on a literal ancestry event

Assemble the geometric and topological inputs of Morgan--Tian Proposition
15.12 (p. 365) on the actual components in Definition 18.2 (pp. 419-420).
These are the local comparison inputs used before Proposition 18.18,
pp. 430-431; no provider or component is replaced by a fresh choice.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT

/-- The actual event input on the specified component path, with the full
retained region and guarded separating neck spheres (Proposition 15.12,
p. 365, and the class transport on pp. 430-431). -/
noncomputable def m57EventInput
    (P02 : RepairedClosedTopologyProvider.{u}) (G53 : RepairedSphereSeparationTheory.{u})
    {g₀ : StandardInitialMetric} (D : RepairedSurgeryFlowData.{u} g₀)
    (L : RawLocalSurgeryTopologyData D.flow) (P : M56PoincareAncestryData D.flow L)
    {T : ℝ} (A : RepairedComponentPath D.flow T P.witness)
    (S : Set.Icc (0 : ℝ) T) (hS : S.1 ∈ D.flow.surgery_times)
    [Nonempty (D.flow.slice S.1).carrier] : RepairedComparisonHomotopyInput D S.1 hS := by
  let sMinus : Set.Icc (0 : ℝ) T :=
    ⟨(D.flow.event S.1 hS).tMinus,
      (D.flow.event S.1 hS).tMinus_nonnegative,
      (D.flow.event S.1 hS).tMinus_lt.le.trans S.2.2⟩
  let parent := A.component sMinus
  let child := A.component S
  letI : SimplyConnectedSpace parent.carrier.carrier :=
    P.component_simply_connected sMinus.1 (A.time_subset sMinus.2) parent
  letI : SimplyConnectedSpace child.carrier.carrier :=
    P.component_simply_connected S.1 (A.time_subset S.2) child
  exact
    { topology := Classical.choice (L.nonempty_reconstruction S.1 hS)
      parent := parent
      child := child
      topology_child := by
        rw [← P.topology_source S.1 hS (inferInstance : Nonempty (D.flow.slice S.1).carrier)]
        exact ⟨A.event_survivor_index S hS inferInstance,
          A.event_survivor_index_kind S hS inferInstance,
          (A.event_survivor S hS inferInstance).1.symm⟩
      admissible := L.admissible
      parent_metric := fun t => m57ComponentMetric parent ((D.flow.event S.1 hS).pre_flow.metric t)
      child_metric := m57ComponentMetric child (D.flow.metric S.1)
      parent_pullback := fun t => m57ComponentMetric_pullback parent
        ((D.flow.event S.1 hS).pre_flow.metric t.1)
      child_pullback := m57ComponentMetric_pullback child (D.flow.metric S.1)
      separating := m57NeckSphere_separating P02 G53 D S.1 hS parent
      retained := {x | parent.inclusion x ∈ interior (D.flow.event S.1 hS).retained_pre ∧
        (D.flow.event S.1 hS).retention.map (parent.inclusion x) ∈ Set.range child.inclusion}
      retained_eq := rfl
      retained_open := m57RetainedRegion_isOpen D S.1 hS parent child
      retained_subset := fun _ hx => hx.1
      retained_to_child := fun _ hx => hx.2
      inherited := A.surgery_transition_inherited S hS inferInstance
      parent_simply_connected := inferInstance
      child_simply_connected := inferInstance
      parent_orientation := Classical.choice (m57ComponentOrientation parent) }

end PoincareMT
