import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
Adapted from Mapher `PoincareMT/Proofs/M49/Mathlib/PartialChartMeasurable.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Borel sets under partial charts

The measure argument for Morgan-Tian Theorem 11.19(1), p. 279, and
Lemma 17.12, p. 410, only uses maps restricted to their chart domains.
These facts make no measurability assertion about totalized chart maps.
-/

set_option autoImplicit false

open Set MeasureTheory

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Restricted chart preimages are Borel, as used in the volume argument
for MT Theorem 11.19(1), p. 279, and Lemma 17.12, p. 410. -/
theorem measurableSet_preimage_inter_source (e : OpenPartialHomeomorph X Y)
    {D : Set Y} (hD : MeasurableSet D) : MeasurableSet (e ⁻¹' D ∩ e.source) := by
  have hsub : MeasurableSet ((Subtype.val : e.source → X) ⁻¹' (e ⁻¹' D)) :=
    hD.preimage e.continuousOn.domRestrict.measurable
  simpa only [Subtype.range_coe] using
    (MeasurableEmbedding.subtype_coe e.open_source.measurableSet).measurableSet_preimage.mp hsub

/-- Borel sets inside a chart domain have Borel images, as used in the
volume argument for MT Theorem 11.19(1), p. 279, and Lemma 17.12, p. 410. -/
theorem measurableSet_image_of_subset_source (e : OpenPartialHomeomorph X Y)
    {C : Set X} (hC : MeasurableSet C) (hCs : C ⊆ e.source) :
    MeasurableSet (e '' C) := by
  rw [e.image_eq_target_inter_inv_preimage hCs, inter_comm]
  exact e.symm.measurableSet_preimage_inter_source hC

end OpenPartialHomeomorph
