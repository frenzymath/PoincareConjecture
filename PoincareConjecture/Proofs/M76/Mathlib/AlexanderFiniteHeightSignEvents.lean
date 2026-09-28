import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveRecenter











set_option autoImplicit false

open Set

namespace Geometry.AlexanderSectionProfile

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]






def HasFiniteHeightSignEvents (W : AlexanderSectionProfile E) : Prop :=
  ∃ C : Set ℝ, C.Finite ∧
    ∀ x ∈ W.carrier, W.height x ∉ C →
      x ∈ closure (W.carrier ∩ {y | W.height y < W.height x}) ∧
        x ∈ closure (W.carrier ∩ {y | W.height x < W.height y})





theorem HasFiniteHeightSignEvents.recenter {W : AlexanderSectionProfile E}
    (hW : W.HasFiniteHeightSignEvents) (c : ℝ) :
    (W.recenter c).HasFiniteHeightSignEvents := by
  obtain ⟨C, hC, hsigns⟩ := hW
  refine ⟨(fun d : ℝ => d + c) ⁻¹' C, ?_, ?_⟩
  · exact hC.preimage (fun _ _ _ _ h => add_right_cancel h)
  · intro x hx hxC
    have hxold : W.height x ∉ C := by
      simpa only [mem_preimage, recenter_height_apply, sub_add_cancel] using hxC
    simpa only [recenter_carrier, recenter_height_apply, sub_lt_sub_iff_right] using
      hsigns x hx hxold

end Geometry.AlexanderSectionProfile
