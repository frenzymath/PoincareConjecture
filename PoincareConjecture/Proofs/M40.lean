import PoincareConjecture.Statements.M40ComparisonHomotopy
import PoincareConjecture.Proofs.M40.ComparisonTransport
import PoincareConjecture.Proofs.M40.SmoothApproximants








set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture




























theorem repairedComparisonHomotopy : RepairedComparisonHomotopyTheory.{u} := by
  constructor
  intro P G39
  obtain ⟨epsilon, hepsilon, _⟩ := G39.comparison
  refine ⟨epsilon, hepsilon, ?_⟩
  intro g₀ D _ K _
  refine ⟨{ transport := ?_ }⟩
  intro T hT _ input hdelta hh
  let Q := Classical.choice
    (K.comparison T hT input.toRepairedComparisonMapInput hdelta hh)
  exact ⟨⟨M40.comparisonHomotopyConclusion P Q
    (M40.comparison_smooth_approximants Q), rfl⟩⟩

end PoincareConjecture
