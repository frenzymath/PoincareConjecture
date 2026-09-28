import PoincareConjecture.Definitions.M23NormalizedKappaCompactness








set_option autoImplicit false

open Set
open scoped Manifold

namespace PoincareConjecture.M23InteriorConvergence

attribute [local instance] FlowCarrier.topologicalSpace

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}

theorem exhaustion_monotone (G : M23InteriorConvergence S) :
    Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing

theorem exists_exhaustion_superset (G : M23InteriorConvergence S)
    {K : Set G.limit.carrier.carrier} (hK : IsCompact K) :
    ∃ j, K ⊆ G.exhaustion j := by
  exact hK.elim_directed_cover G.exhaustion G.exhaustion_open
    (by rw [G.exhaustion_covers]; exact subset_univ _) G.exhaustion_monotone.directed_le

end PoincareConjecture.M23InteriorConvergence
