import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CanonicalPersistence
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.GoodPointAssembly
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.UnitLifetimeOfGoodPoints
import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.NoncollapsingCertificate
import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.ScalarPositivity
import PoincareConjecture.Proofs.M34.Thm12_5_Existence.PartialFlowCompleteness










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34





theorem standardFlow_lifetime_ge_one (P : M34StandardCapPredecessors)
    {g0 : StandardInitialMetric} (F : MaximalStandardCapFlow g0) :
    1 ≤ F.base.lifetime := by
  obtain ⟨epsilon, hepsilon, hsmall, long⟩ := P.long_limits
  obtain ⟨c, hc, hpersistence⟩ := exists_ordinary_canonical_persistence
    P.kappa_alternatives hepsilon (hsmall.trans (by norm_num))
  obtain ⟨A, hA, hthreshold⟩ := standardFlow_chapter11_goodPoint_threshold_of_persistence P
  obtain ⟨R, _⟩ := P.ordinary_product (EuclideanSpace ℝ (Fin 3))
    (partialFlowSpacetimeInterval F.base) F.base.flow
  obtain ⟨E0⟩ := standardCapEstimate_exists g0
  obtain ⟨H⟩ := standardFlow_noncollapsingCertificate F P
  have hcomplete : ∀ t ∈ (partialFlowSpacetimeInterval F.base).domain,
      MetricComplete (F.base.flow.metric t) :=
    fun _ ht => partialFlow_complete F.base P.curvature ht
  have hpersist := hpersistence (I := partialFlowSpacetimeInterval F.base)
    F.base.flow R hcomplete
  obtain ⟨Q, _hQ, hgood⟩ := hthreshold F R E0 H
    (epsilon0 := epsilon) (epsilon := epsilon) (c := c) long hepsilon le_rfl hc
    (fun p hp hd Conv K => hpersist p hp hd Conv K)
  exact standardFlow_lifetime_ge_one_of_good_points F P R E0 H
    long hepsilon le_rfl hc hA (Rstar := Q) hgood

end PoincareConjecture.M34
