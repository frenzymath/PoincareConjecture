import Mathlib.Logic.Small.Basic
import Mathlib.Topology.Instances.Shrink
import Mathlib.Topology.Separation.Basic

universe u

namespace Poincare.Topology.SecondCountable

variable (X : Type u) [TopologicalSpace X] [T0Space X] [SecondCountableTopology X]

theorem exists_injective_set_nat :
    Exists fun f : X -> Set Nat => Function.Injective f := by
  obtain ⟨b, hb⟩ := TopologicalSpace.exists_seq_basis X
  refine ⟨fun x => {i | x ∈ b i}, ?_⟩
  intro x y hxy
  apply hb.eq_iff.mpr
  rintro s ⟨i, rfl⟩
  exact Set.ext_iff.mp hxy i

theorem small : Small.{0} X := by
  obtain ⟨f, hf⟩ := exists_injective_set_nat X
  exact small_of_injective hf

noncomputable def homeomorphShrink :
    letI : Small.{0} X := small X
    Homeomorph X (Shrink.{0} X) := by
  letI : Small.{0} X := small X
  exact Shrink.homeomorph X

theorem exists_homeomorph_small :
    Exists fun Y : Type => Exists fun _ : TopologicalSpace Y =>
      Nonempty (Homeomorph X Y) := by
  let : Small.{0} X := small X
  exact ⟨Shrink.{0} X, inferInstance, ⟨homeomorphShrink X⟩⟩

end Poincare.Topology.SecondCountable
