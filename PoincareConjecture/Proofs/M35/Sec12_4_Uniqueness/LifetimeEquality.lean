import PoincareConjecture.Proofs.M35.RawFlow.Splicing

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.MaximalStandardCapFlow

theorem partial_lifetime_le_of_metric_agreement
    {g₀ : StandardInitialMetric} (F : MaximalStandardCapFlow g₀)
    (G : PartialStandardCapFlow g₀)
    (hmetric : Set.EqOn F.metric G.flow.metric
      (Set.Ico 0 F.base.lifetime ∩ Set.Ico 0 G.lifetime)) :
    G.lifetime ≤ F.base.lifetime := by
  by_contra hle
  have hlt : F.base.lifetime < G.lifetime := lt_of_not_ge hle
  have hagree : Set.EqOn F.base.flow.metric G.flow.metric
      (Set.Ico 0 F.base.lifetime) := by
    intro t ht
    exact hmetric ⟨ht, ht.1, ht.2.trans hlt⟩
  exact F.maximal G.lifetime ⟨F.base.extensionOfMetricAgreement G hlt hagree⟩

theorem lifetime_eq_of_metric_agreement
    {g₀ : StandardInitialMetric} (F G : MaximalStandardCapFlow g₀)
    (hmetric : Set.EqOn F.metric G.metric
      (Set.Ico 0 F.base.lifetime ∩ Set.Ico 0 G.base.lifetime)) :
    F.base.lifetime = G.base.lifetime := by
  apply le_antisymm
  · apply G.partial_lifetime_le_of_metric_agreement F.base
    intro t ht
    exact (hmetric ⟨ht.2, ht.1⟩).symm
  · exact F.partial_lifetime_le_of_metric_agreement G.base hmetric

end PoincareConjecture.MaximalStandardCapFlow
