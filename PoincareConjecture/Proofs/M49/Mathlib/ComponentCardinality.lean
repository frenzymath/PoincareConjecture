import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

universe u v

theorem Homeomorph.card_connectedComponents_eq
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) :
    Nat.card (ConnectedComponents X) = Nat.card (ConnectedComponents Y) := by
  apply Nat.card_eq_of_bijective e.continuous.connectedComponentsMap
  refine ⟨?_, e.continuous.connectedComponentsMap_surjective e.surjective⟩
  intro c d h
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe d
  have hi := congrArg e.symm.continuous.connectedComponentsMap h
  simpa only [Continuous.connectedComponentsMap_mk, Homeomorph.symm_apply_apply] using hi
