import PoincareConjecture.Proofs.M34.Thm12_5_Existence.ShortTimeExistence
import PoincareConjecture.Proofs.M34.Thm12_5_Existence.FiniteLifetime
import PoincareConjecture.Proofs.M34.Thm12_5_Existence.BoundedMaximality

set_option autoImplicit false

open Set

namespace PoincareConjecture.M34

theorem maximalStandardCapFlow_exists (P : M34StandardCapPredecessors)
    (g0 : StandardInitialMetric) :
    ∃ F : MaximalStandardCapFlow g0,
      ∀ t ∈ Ico 0 F.base.lifetime, MetricComplete (F.metric t) := by
  obtain ⟨E0⟩ := standardCapEstimate_exists g0
  obtain ⟨F0, _hcomplete, _hbound⟩ := completePartialStandardCapFlow_exists P g0
  obtain ⟨F⟩ := maximalStandardCapFlow_exists_of_bounded_lifetimes F0
    (partialFlow_lifetime_le_scalar_bound P.curvature E0)
  exact ⟨F, fun _ ht => partialFlow_complete F.base P.curvature ht⟩

end PoincareConjecture.M34
