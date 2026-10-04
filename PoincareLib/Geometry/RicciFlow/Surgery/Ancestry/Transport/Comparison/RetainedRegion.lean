import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Map

/-!
# The full retained region on the selected parent

The open region in Morgan--Tian Proposition 15.12 (p. 365) is restricted to
the actual child component. Continuity is used only on the interior of the
displayed retained set, the domain where the retention map is supplied.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT

/-- Openness of exactly the full retained set in Proposition 15.12, p. 365. -/
theorem m57RetainedRegion_isOpen
    {g₀ : StandardInitialMetric} (D : RepairedSurgeryFlowData.{u} g₀)
    (T : ℝ) (hT : T ∈ D.flow.surgery_times)
    [Nonempty (D.flow.slice T).carrier]
    (parent : SurgerySelectedComponent (D.flow.slice (D.flow.event T hT).tMinus))
    (child : SurgerySelectedComponent (D.flow.slice T)) :
    IsOpen {x | parent.inclusion x ∈ interior (D.flow.event T hT).retained_pre ∧
      (D.flow.event T hT).retention.map (parent.inclusion x) ∈
        Set.range child.inclusion} := by
  have hret := (D.flow.event T hT).retention.map_smooth.continuousOn.mono
    (interior_subset (s := (D.flow.event T hT).retained_pre))
  exact (hret.isOpen_inter_preimage isOpen_interior
    child.inclusion_openEmbedding.isOpen_range).preimage parent.inclusion_smooth.continuous

end PoincareMT
