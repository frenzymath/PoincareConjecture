import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Spacetime.GeneralizedBoxMetric
import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.Geometry
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Basic

/-!
# Intrinsic Ricci geometry of the actual generalized-flow atlas

Use the checked M11 interval realization. M12's cover converse uses the
original box flows, metrics, connections and within-time equations; it
produces the intrinsic equation on this same spacetime. The M14 transport
is a checked projection, not an additional geometric hypothesis.
Source: Morgan--Tian Definitions 3.34-3.38 and Remark 3.37, pp. 59-61.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.EpochExtension.Spacetime

variable (F : GeneralizedRicciFlowData.{u})

/-- One selected spacetime with exact original-slice identifications and PDE. -/
structure FlowBoxRicciGeometry where
  realization : GeneralizedFlowCarrierConclusionWithInterval (flowBoxAtlas F)
  sliceIdentification : ∀ t,
    SpacetimeSliceIdentification realization.spacetime t (realization.slices t)
      (flowSliceLabel F t)
  leafwise : LeafwiseLeviCivitaFamily realization.spacetime realization.slices
  equation : IntrinsicGeneralizedRicciEquation leafwise

theorem originalBoxes_cover (R : GeneralizedFlowCarrierConclusionWithInterval (flowBoxAtlas F)) :
    ∀ p : R.spacetime.Point, ∃ b,
      ∃ q : (R.timeIntervals.interval (boxInterval F b)).Point × (F.box b).carrier.carrier,
        (originalBoxCylinder F R b).toSpacetime q = p := by
  rintro ⟨t, x⟩
  obtain ⟨b, ht, y, hy⟩ := F.box_covers t x
  exact ⟨b, (⟨t, ht⟩, y), congrArg (fun z => (⟨t, z⟩ : F.point)) hy⟩

/-- The original ordinary equations imply the intrinsic equation on any
selected realization and its supplied M12 leafwise connection. -/
theorem originalBoxes_ricciEquation
    (R : GeneralizedFlowCarrierConclusionWithInterval (flowBoxAtlas F))
    (D : LeafwiseLeviCivitaFamily R.spacetime R.slices)
    (h : GeneralizedRicciGaugeTheory.{u} 3) :
    IntrinsicGeneralizedRicciEquation D := by
  have G := h.gauges F.point Sigma.fst (flowInterval F) R.spacetime R.slices
    R.timeIntervals R.gaugeCover D
  exact G.cover_converse F.box_index (fun b => (F.box b).carrier.carrier)
    (boxInterval F) (originalBoxCylinder F R) (originalBoxMetric F R)
    (fun b => (F.box b).flow.connection) (originalBoxes_cover F R)
    (fun b => (F.box b).flow.equation)

/-- Every generalized flow with the specified boxes has the same-carrier
M11/M12 realization. Both predecessor services are explicitly supplied. -/
theorem flowBoxRicciGeometry
    (hM11 : GeneralizedSpacetimeGeometryTheory.{u} 3)
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3) : Nonempty (FlowBoxRicciGeometry F) := by
  classical
  obtain ⟨R⟩ := flowBoxAtlas_realize F hM11
  obtain ⟨D⟩ := (hM12.leafwise_calculus F.point Sigma.fst (flowInterval F)
    R.spacetime R.slices R.timeIntervals R.gaugeCover).1
  exact ⟨⟨R, fun t => Classical.choice (flowSlice_identification F R t), D,
    originalBoxes_ricciEquation F R D hM12⟩⟩

/-- The transport used by L-geometry retains the selected spacetime exactly. -/
noncomputable def FlowBoxRicciGeometry.toLGeometry (G : FlowBoxRicciGeometry F) :
    GeneralizedLGeometryTransport 3 F.point Sigma.fst (flowInterval F) where
  spacetime := G.realization.spacetime
  slices := G.realization.slices
  timeIntervals := G.realization.timeIntervals
  gaugeCover := G.realization.gaugeCover
  leafwise := G.leafwise
  ricciEquation := G.equation

end PoincareMT.EpochExtension.Spacetime
