import PoincareConjecture.Statements.M35StandardCapUniqueness
import PoincareConjecture.Statements.M35Providers
import PoincareConjecture.Proofs.M35.Sec12_4_Uniqueness.LifetimeEquality
import PoincareConjecture.Proofs.M35.Sec12_4_Uniqueness.PartialUniqueness
import PoincareConjecture.Proofs.M35.CapGeometry.IndependentScalarRate
import PoincareConjecture.Proofs.M35.CapGeometry.CanonicalAlternatives









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture










































theorem repairedStandardCapUniqueness (P : M35StandardCapPredecessors) :
    RepairedStandardCapUniquenessTheory := by
  refine ⟨?_⟩
  intro g₀ E
  have hunique (G : PartialStandardCapFlow g₀) (t : ℝ)
      (ht : t ∈ Set.Ico 0 E.flow.base.lifetime ∩ Set.Ico 0 G.lifetime) :=
    E.partial_metric_unique P.curvature G ht
  refine ⟨{
    lifetime_one := E.lifetime_one
    complete := E.complete
    unique_lifetime := ?_
    unique_metric := fun G t ht => hunique G.base t ht
    partial_unique_metric := hunique
    scalar_lower_bound := E.scalar_lower_rate_from_unit_time P
    canonical := M35.Uniqueness.standard_cap_canonical P E
  }⟩
  intro G
  exact E.flow.lifetime_eq_of_metric_agreement G (fun t ht => hunique G.base t ht)

end PoincareConjecture
