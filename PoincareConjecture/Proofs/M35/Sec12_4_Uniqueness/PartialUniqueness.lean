import PoincareConjecture.Definitions.M35StandardCapUniqueness
import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.Uniqueness

set_option autoImplicit false

namespace PoincareConjecture.RepairedStandardCapExistenceData

theorem partial_metric_unique (P : RicciFlowCurvatureTheory.{0})
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (G : PartialStandardCapFlow g₀) {t : ℝ}
    (ht : t ∈ Set.Ico 0 E.flow.base.lifetime ∩ Set.Ico 0 G.lifetime) :
    E.flow.metric t = G.flow.metric t :=
  M34.partialStandardCapFlow_metric_unique P E.initial_estimate E.flow.base G
    g₀.cylindrical_end ht

end PoincareConjecture.RepairedStandardCapExistenceData
