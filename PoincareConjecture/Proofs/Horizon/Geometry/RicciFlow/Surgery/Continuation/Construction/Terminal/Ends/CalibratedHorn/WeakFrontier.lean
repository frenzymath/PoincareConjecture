import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Frontier

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {H : SingularTimeAssumptions G T M}

theorem exists_end_region_of_low_point (Q : SingularLimitConclusion H)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K) (q : ℝ)
    (hlow : ∃ x ∈ K.component, Q.terminal_scalar x ≤ q) :
    ∃ (n : ℕ) (X : Set (Q.extension.extended.slice T).carrier),
      IsClosed X ∧ IsConnected X ∧ X ⊆ K.component ∧
      Subtype.val '' e.tail n ⊆ X ∧ ¬ IsCompact X ∧
      (∀ x ∈ X, q ≤ Q.terminal_scalar x) ∧
      (∃ x ∈ X, Q.terminal_scalar x = q) ∧ IsCompact (frontier X) ∧
      ∀ x ∈ frontier X, Q.terminal_scalar x = q := by
  by_cases hstrict : ∃ x ∈ K.component, Q.terminal_scalar x < q
  · exact Q.exists_end_superlevel_region_compact_frontier K e q hstrict
  · let : LocallyConnectedSpace (Q.extension.extended.slice T).carrier :=
      ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) _
    have hclosed : IsClosed K.component := K.component_eq ▸ isClosed_connectedComponent
    have hopen : IsOpen K.component := K.component_eq ▸ isOpen_connectedComponent
    have hfront : frontier K.component = ∅ := (show IsClopen K.component from ⟨hclosed, hopen⟩).frontier_eq
    have hbound : ∀ x ∈ K.component, q ≤ Q.terminal_scalar x :=
      fun x hx => le_of_not_gt (fun h => hstrict ⟨x, hx, h⟩)
    obtain ⟨x, hx, hlow⟩ := hlow
    refine ⟨0, K.component, hclosed, K.component_eq ▸ isConnected_connectedComponent,
      subset_rfl, ?_, e.not_isCompact_component, hbound,
      ⟨x, hx, le_antisymm hlow (hbound x hx)⟩, ?_, ?_⟩
    · rintro y ⟨z, _, rfl⟩
      exact z.property
    · rw [hfront]
      exact isCompact_empty
    · intro y hy
      rw [hfront] at hy
      exact hy.elim

end PoincareConjecture.SingularLimitConclusion
