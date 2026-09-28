import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic









set_option autoImplicit false

open Set MeasureTheory

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]



theorem measurableSet_preimage_inter_source (e : OpenPartialHomeomorph X Y)
    {D : Set Y} (hD : MeasurableSet D) : MeasurableSet (e ⁻¹' D ∩ e.source) := by
  have hsub : MeasurableSet ((Subtype.val : e.source → X) ⁻¹' (e ⁻¹' D)) :=
    hD.preimage e.continuousOn.domRestrict.measurable
  simpa only [Subtype.range_coe] using
    (MeasurableEmbedding.subtype_coe e.open_source.measurableSet).measurableSet_preimage.mp hsub



theorem measurableSet_image_of_subset_source (e : OpenPartialHomeomorph X Y)
    {C : Set X} (hC : MeasurableSet C) (hCs : C ⊆ e.source) :
    MeasurableSet (e '' C) := by
  rw [e.image_eq_target_inter_inv_preimage hCs, inter_comm]
  exact e.symm.measurableSet_preimage_inter_source hC

end OpenPartialHomeomorph
