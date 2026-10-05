import Mathlib.Logic.Small.Basic
import Mathlib.Topology.Instances.Shrink
import Mathlib.Topology.Separation.Basic

/-!
# Small models of second-countable separated spaces

A countable basis separates points of a T0 space, giving an injection into
`Set Nat`. Consequently the carrier is `Small.{0}` in every ambient universe.
The smallness theorem is explicit rather than a global instance; mathlib's
`Shrink` construction supplies the induced topology and the homeomorphism.
-/

universe u

namespace Poincare.Topology.SecondCountable

variable (X : Type u) [TopologicalSpace X] [T0Space X] [SecondCountableTopology X]

/-- Record a point by the indices of the basis elements containing it. -/
theorem exists_injective_set_nat :
    Exists fun f : X -> Set Nat => Function.Injective f := by
  obtain ⟨b, hb⟩ := TopologicalSpace.exists_seq_basis X
  refine ⟨fun x => {i | x ∈ b i}, ?_⟩
  intro x y hxy
  apply hb.eq_iff.mpr
  rintro s ⟨i, rfl⟩
  exact Set.ext_iff.mp hxy i

/-- Every second-countable T0 space has a carrier in universe zero. -/
theorem small : Small.{0} X := by
  obtain ⟨f, hf⟩ := exists_injective_set_nat X
  exact small_of_injective hf

/-- The universe-zero model with topology pulled back along `equivShrink`. -/
noncomputable def homeomorphShrink :
    letI : Small.{0} X := small X
    Homeomorph X (Shrink.{0} X) := by
  letI : Small.{0} X := small X
  exact Shrink.homeomorph X

/-- A second-countable T0 space is homeomorphic to a space in universe zero. -/
theorem exists_homeomorph_small :
    Exists fun Y : Type => Exists fun _ : TopologicalSpace Y =>
      Nonempty (Homeomorph X Y) := by
  let : Small.{0} X := small X
  exact ⟨Shrink.{0} X, inferInstance, ⟨homeomorphShrink X⟩⟩

end Poincare.Topology.SecondCountable
