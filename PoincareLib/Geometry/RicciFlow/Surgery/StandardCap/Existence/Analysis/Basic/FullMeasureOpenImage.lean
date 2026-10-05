import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.ContinuousOn

/-!
# Open preimages under maps with full-measure image

Restricting a continuous map on an open domain to an open target set
preserves that target set's measure whenever the original image is full.
This is the measure step in Morgan-Tian Proposition 12.13, pp. 304-306.
-/

set_option autoImplicit false

open Set MeasureTheory

namespace PoincareMT.M34

/-- A full-measure image intersects each open target set in the image
of an open subset of the original domain (Proposition 12.13). -/
theorem exists_open_image_measure_eq {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace Y]
    {f : X → Y} {S : Set X} (hS : IsOpen S) (hf : ContinuousOn f S)
    (mu : Measure Y) (hfull : mu (f '' S)ᶜ = 0)
    {B : Set Y} (hB : IsOpen B) :
    ∃ W : Set X, IsOpen W ∧ W ⊆ S ∧ f '' W ⊆ B ∧ mu (f '' W) = mu B := by
  refine ⟨S ∩ f ⁻¹' B, hf.isOpen_inter_preimage hS hB, inter_subset_left, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  · rw [image_inter_preimage]
    exact Measure.measure_inter_eq_of_ae (ae_iff.mpr hfull)

end PoincareMT.M34
