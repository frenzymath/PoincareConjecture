import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.ContinuousOn









set_option autoImplicit false

open Set MeasureTheory

namespace PoincareConjecture.M34



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

end PoincareConjecture.M34
