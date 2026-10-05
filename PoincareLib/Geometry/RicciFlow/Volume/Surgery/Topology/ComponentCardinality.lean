import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.SetTheory.Cardinal.Finite

/-!
Adapted from Mapher `PoincareMT/Proofs/M49/Mathlib/ComponentCardinality.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Component cardinality under a homeomorphism

Morgan-Tian Lemma 17.12, pp. 410-411, transports component counts
along the actual ordinary-flow and pre-event identifications.
An equivalence of the actual component quotients gives the exact
cardinality equality, including empty or infinite component types.
-/

set_option autoImplicit false

universe u v

/-- A homeomorphism preserves the cardinality of the actual component
quotient (the topology bridge for MT Lemma 17.12, pp. 410-411).
The proof gives a bijection before applying `Nat.card`. -/
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
