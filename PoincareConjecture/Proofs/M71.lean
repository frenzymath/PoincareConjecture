import PoincareConjecture.Proofs.M70
import PoincareConjecture.Proofs.M71.TerminalEvent
import PoincareConjecture.Proofs.M71.WidthInputs
import PoincareConjecture.Proofs.M71.ContinuationInputs
import PoincareConjecture.Proofs.M71.Thm18_1_NegativeProfile
import PoincareConjecture.Proofs.M71.Thm18_1_EmptySlice
import PoincareConjecture.Statements.M71FiniteExtinction

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem m71GlobalFiniteExtinction
    : M71GlobalFiniteExtinctionStatement.{u} := by
  intro M _ _ _ _ _ _ _ _ _ N G input hM67 hM68 hM69
  have hT := m71ExtinctionTime_mem input
  have hempty := m71EmptySlice input.continuation hM67 hM68 hM69
    (m71ExtinctionTime input.continuation) hT
    (m71ExtinctionTime_nonneg input.continuation)
    (m71Profile_neg_at_extinctionTime input.continuation hM67)
  rw [input.flow_eq] at hT hempty
  obtain ⟨E, _hET, _hfirst⟩ := m71FirstEmptySurgery G.certificate
    (m71ExtinctionTime input.continuation) hT hempty
  exact ⟨E⟩

end PoincareConjecture
