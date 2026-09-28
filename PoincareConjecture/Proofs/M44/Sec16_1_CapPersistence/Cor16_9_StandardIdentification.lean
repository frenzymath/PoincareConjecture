import PoincareConjecture.Definitions.M35StandardCapUniqueness

set_option autoImplicit false

namespace PoincareConjecture

namespace RepairedStandardCapUniquenessData

variable {g₀ : StandardInitialMetric} {E : RepairedStandardCapExistenceData g₀}
  (U : RepairedStandardCapUniquenessData g₀ E)

include U

theorem model_lifetime_one (G : MaximalStandardCapFlow g₀) : G.base.lifetime = 1 :=
  (U.unique_lifetime G).symm.trans U.lifetime_one

theorem model_metric_eq (G : MaximalStandardCapFlow g₀)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) : E.flow.metric t = G.metric t := by
  apply U.unique_metric G t
  simpa only [U.lifetime_one, U.model_lifetime_one G, Set.inter_self] using ht

theorem partial_metric_eq (G : PartialStandardCapFlow g₀)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) (hG : t < G.lifetime) :
    G.flow.metric t = E.flow.metric t := by
  symm
  apply U.partial_unique_metric G t
  exact ⟨by simpa only [U.lifetime_one] using ht, ht.1, hG⟩

theorem partial_metric_eq_model (G : PartialStandardCapFlow g₀)
    (S : MaximalStandardCapFlow g₀) {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) 1) (hG : t < G.lifetime) :
    G.flow.metric t = S.metric t :=
  (U.partial_metric_eq G ht hG).trans (U.model_metric_eq S ht)

end RepairedStandardCapUniquenessData

end PoincareConjecture
