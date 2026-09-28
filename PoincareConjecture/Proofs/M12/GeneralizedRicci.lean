import PoincareConjecture.Proofs.M12.GeneralizedBoxMetric
import PoincareConjecture.Statements.M12GeneralizedEquation
import PoincareConjecture.Definitions.M14GeneralizedLGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M12

variable (F : GeneralizedRicciFlowData.{u})

structure FlowBoxRicciGeometry where
  realization : GeneralizedFlowCarrierConclusion (flowBoxAtlas F)
  sliceIdentification : ∀ t,
    SpacetimeSliceIdentification realization.spacetime t (realization.slices t)
      (flowSliceLabel F t)
  leafwise : LeafwiseLeviCivitaFamily realization.spacetime realization.slices
  equation : IntrinsicGeneralizedRicciEquation leafwise

theorem originalBoxes_cover (R : GeneralizedFlowCarrierConclusion (flowBoxAtlas F)) :
    ∀ p : R.spacetime.Point, ∃ b,
      ∃ q : (R.timeIntervals.interval (boxInterval F b)).Point × (F.box b).carrier.carrier,
        (originalBoxCylinder F R b).toSpacetime q = p := by
  rintro ⟨t, x⟩
  obtain ⟨b, ht, y, hy⟩ := F.box_covers t x
  exact ⟨b, (⟨t, ht⟩, y), congrArg (fun z => (⟨t, z⟩ : F.point)) hy⟩

theorem originalBoxes_ricciEquation
    (R : GeneralizedFlowCarrierConclusion (flowBoxAtlas F))
    (D : LeafwiseLeviCivitaFamily R.spacetime R.slices)
    (h : GeneralizedRicciGaugeTheory.{u} 3) :
    IntrinsicGeneralizedRicciEquation D := by
  have G := h.gauges F.point Sigma.fst (flowInterval F) R.spacetime R.slices
    R.timeIntervals R.gaugeCover D
  exact G.cover_converse F.box_index (fun b => (F.box b).carrier.carrier)
    (boxInterval F) (originalBoxCylinder F R) (originalBoxMetric F R)
    (fun b => (F.box b).flow.connection) (originalBoxes_cover F R)
    (fun b => (F.box b).flow.equation)

theorem flowBoxRicciGeometry
    (hM11 : GeneralizedSpacetimeGeometryTheory.{u} 3)
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3) : Nonempty (FlowBoxRicciGeometry F) := by
  classical
  obtain ⟨R⟩ := flowBoxAtlas_realize F hM11
  obtain ⟨D⟩ := (hM12.leafwise_calculus F.point Sigma.fst (flowInterval F)
    R.spacetime R.slices R.timeIntervals R.gaugeCover).1
  exact ⟨⟨R, fun t => Classical.choice (flowSlice_identification F R t), D,
    originalBoxes_ricciEquation F R D hM12⟩⟩

noncomputable def FlowBoxRicciGeometry.toLGeometry (G : FlowBoxRicciGeometry F) :
    GeneralizedLGeometryTransport 3 F.point Sigma.fst (flowInterval F) where
  spacetime := G.realization.spacetime
  slices := G.realization.slices
  timeIntervals := G.realization.timeIntervals
  gaugeCover := G.realization.gaugeCover
  leafwise := G.leafwise
  ricciEquation := G.equation

end PoincareConjecture.Proofs.M12
