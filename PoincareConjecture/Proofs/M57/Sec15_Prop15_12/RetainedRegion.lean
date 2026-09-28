import PoincareConjecture.Definitions.M39ComparisonMap









set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture


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

end PoincareConjecture
