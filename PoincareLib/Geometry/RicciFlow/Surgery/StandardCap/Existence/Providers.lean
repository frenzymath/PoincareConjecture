import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.ExistenceTheory
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.Kappa
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.Blowup

/-!
# Applied earlier theorem services for M34

M27's provider imports the actual M03/M04/M07, M08-M10, M12-M15 and
M22 producers used below. This supplier does not import the M34 entry,
so the entry can apply it without an import cycle. These checked
applications add no admission or geometric hypothesis.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT

/-- Supply the source-reviewed M34 boundary from actual earlier milestones.
The M22 operation applies to the ancient solution selected by M30, and the
M30 long-limit threshold is retained from the same selected limit service. -/
theorem m34StandardCapPredecessorsFromMilestones :
    M34StandardCapPredecessors := by
  have h12 : GeneralizedRicciGaugeTheory.{0} 3 :=
    generalizedRicciGaugeGeometry_from_M03_M04_M11 3
  have h13 : GeneralizedParabolicRescalingTheory.{0} 3 :=
    generalizedParabolicRescaling_from_M12 3
  have h14 : GeneralizedLGeometryTheory.{0} 3 :=
    generalizedLGeometryTheory_from_predecessors 3
  let C22 : UniversalNoncollapsingConclusion.{0} 3 :=
    Classical.choice (m22UniversalNoncollapsingFromMilestones 3)
  refine {
    local_flow := ?_
    curvature := ricciFlowCurvatureTheory
    pointed_compactness := fun H => pointedRicciFlowCompactness_from_M04 H
    ordinary_windows := m15OrdinaryProvidersFromMilestones 3
    ordinary_product := h12.ordinary_flow
    ordinary_rescaling := h13.ordinary_flow
    metric_homothety := h13.metric_homothety
    exponential := ?_
    ordinary_capture := ?_
    noncollapse_generalized :=
      (noncollapsingGeneralizedAndCompact_from_predecessors 3).generalized.uniform
    zero_avr := @C22.asymptotic_volume_ratio_zero
    kappa_alternatives := m27KappaAlternativesFromMilestones
    long_limits := ?_
  }
  · intro n M _ _ _ _ _ _
    exact ricciFlowLocalTheory
  · intro X _ time I G
    obtain ⟨Q⟩ := h14.conclusion X time I G
    exact ⟨Q.exponential⟩
  · intro X _ time I G O
    obtain ⟨Q⟩ := h14.conclusion X time I G
    exact Q.ordinary_capture O
  · obtain ⟨epsilon₀, hpos, hle, _short, hlong⟩ :=
      m30ControlledGeneralizedBlowupLimitsFromMilestones.{0}.limits
    exact ⟨epsilon₀, hpos, hle, hlong⟩

end PoincareMT
