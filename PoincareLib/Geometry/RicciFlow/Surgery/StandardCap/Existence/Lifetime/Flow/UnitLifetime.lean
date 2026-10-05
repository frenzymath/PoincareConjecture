import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.CanonicalGeometry.CanonicalPersistence
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.Basic.GoodPointAssembly
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.Flow.UnitLifetimeOfGoodPoints
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Noncollapsing.NoncollapsingCertificate
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialEstimates.ScalarPositivity
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Flow.PartialFlowCompleteness

/-!
# Every maximal standard cap flow has lifetime at least one

Actual canonical persistence discharges the high-good-point threshold.
The second blow-up volume contradiction then excludes every subunit
lifetime. Source: Morgan-Tian Theorems 12.28-12.29 and Claim 12.30,
pp. 323-325; canonical-lifetime-assembly.md in the M34 task records.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareMT.M34

/-- The actual neck and cap persistence theorems, high-good-point
contradiction and zero-AVR volume contradiction give the unit lifetime
lower bound for every supplied maximal standard flow
(Theorems 12.28-12.29, pp. 323-325). -/
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

end PoincareMT.M34
