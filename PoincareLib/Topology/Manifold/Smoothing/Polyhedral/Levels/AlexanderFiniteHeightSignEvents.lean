import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.AlexanderRecursiveRecenter

/-!
# Finite height events with actual strict approaches elsewhere

The complete profile retains a finite set outside which
every surface point has both strict height approaches.
This is weaker than hereditary signs at all nonisolated
level points and is used to choose regular surgery windows.
See Alexander 1924, pp. 6--8 and M76 derivation 278.
-/

set_option autoImplicit false

open Set

namespace Geometry.AlexanderSectionProfile

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite set contains every possible failure of the
two strict height approaches. The assertion concerns all
actual carrier points outside that set; it leaves event
heights unrestricted. See Alexander pp. 6--8 and
M76 derivation 278. -/
def HasFiniteHeightSignEvents (W : AlexanderSectionProfile E) : Prop :=
  ∃ C : Set ℝ, C.Finite ∧
    ∀ x ∈ W.carrier, W.height x ∉ C →
      x ∈ closure (W.carrier ∩ {y | W.height y < W.height x}) ∧
        x ∈ closure (W.carrier ∩ {y | W.height x < W.height y})

/-- Recenter the same finite height event set by translation.
All pointwise strict-approach sets are unchanged, including
empty carriers and empty event sets. See Alexander p. 7
and M76 derivation 278. -/
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
