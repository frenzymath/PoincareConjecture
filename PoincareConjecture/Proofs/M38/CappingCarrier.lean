import PoincareConjecture.Proofs.M38.CappingCompact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

noncomputable def cappedDiscardedCarrier : GeneralizedSliceCarrier.{u} := by
  letI := cappedDiscardedChartedSpace F T hT P
  letI := cappedDiscardedSpace_isManifold F T hT P
  letI := cappedDiscardedSpace_t2 F T hT P
  letI := cappedDiscardedSpace_compact F T hT P
  letI : MeasurableSpace (CappedDiscardedSpace F T hT P) :=
    borel (CappedDiscardedSpace F T hT P)
  exact {
    carrier := CappedDiscardedSpace F T hT P
    topologicalSpace := inferInstance
    measurableSpace := inferInstance
    borelSpace := ⟨rfl⟩
    chartedSpace := cappedDiscardedChartedSpace F T hT P
    isManifold := inferInstance
    t2Space := inferInstance
    t3Space := inferInstance
    secondCountable := ChartedSpace.secondCountable_of_sigmaCompact StandardCapSpace _ }

theorem cappedDiscardedCarrier_compact :
    IsCompact (Set.univ : Set (cappedDiscardedCarrier F T hT P).carrier) := by
  change IsCompact (Set.univ : Set (CappedDiscardedSpace F T hT P))
  letI := cappedDiscardedSpace_compact F T hT P
  exact isCompact_univ

end PoincareConjecture.M38
