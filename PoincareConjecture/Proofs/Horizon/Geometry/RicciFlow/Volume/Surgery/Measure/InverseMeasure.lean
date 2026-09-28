import PoincareConjecture.Proofs.M10.InverseMeasure
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.OpenPartialHomeomorph.Basic




















set_option autoImplicit false

open MeasureTheory Set

namespace PoincareConjecture.SurgeryVolume.Measure

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]


theorem map_inverse_restrict_apply (e : OpenPartialHomeomorph X Y) (μ : Measure Y)
    {A : Set X} (hA : MeasurableSet A) (hAsource : A ⊆ e.source) :
    ((μ.restrict e.target).map e.symm) A = μ (e '' A) := by
  have hmeas : AEMeasurable e.symm (μ.restrict e.target) :=
    e.symm.continuousOn.aemeasurable e.open_target.measurableSet
  rw [Measure.map_apply_of_aemeasurable hmeas hA,
    Measure.restrict_apply' e.open_target.measurableSet,
    e.image_eq_target_inter_inv_preimage hAsource, inter_comm]

end PoincareConjecture.SurgeryVolume.Measure
