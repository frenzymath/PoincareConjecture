import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
Adapted from Mapher `PoincareMT/Proofs/M10/InverseMeasure.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Pulling a restricted measure through an actual inverse branch

The arbitrary total extensions of a partial homeomorphism need not be
measurable. Restriction to its open target makes the inverse measurable
almost everywhere and yields the exact image formula on source subsets.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace PoincareMT.SurgeryVolume.Measure

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

/-- The inverse pushforward evaluates to the actual image measure on source subsets. -/
theorem map_inverse_restrict_apply (e : OpenPartialHomeomorph X Y) (μ : Measure Y)
    {A : Set X} (hA : MeasurableSet A) (hAsource : A ⊆ e.source) :
    ((μ.restrict e.target).map e.symm) A = μ (e '' A) := by
  have hmeas : AEMeasurable e.symm (μ.restrict e.target) :=
    e.symm.continuousOn.aemeasurable e.open_target.measurableSet
  rw [Measure.map_apply_of_aemeasurable hmeas hA,
    Measure.restrict_apply' e.open_target.measurableSet,
    e.image_eq_target_inter_inv_preimage hAsource, inter_comm]

end PoincareMT.SurgeryVolume.Measure
