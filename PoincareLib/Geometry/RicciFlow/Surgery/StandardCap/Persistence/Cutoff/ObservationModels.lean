import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Cutoff.PreparedCounterexamples
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Comparison.Evolution.StandardIdentification

/-!
# Identifying the actual observation metric

The fixed initial metric and recorded heterogeneous model equality
identify the observation lifetime and metric. M35 then compares with
the selected standard solution without equating connection records.
Morgan--Tian, Corollary 16.9 and Proposition 16.5, pp. 373-374;
M44 derivation 111.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT.M44

private theorem maximal_metric_eq_of_heq
    {g0 g1 : StandardInitialMetric} (hg : g0 = g1)
    (S : MaximalStandardCapFlow g0) (T : MaximalStandardCapFlow g1)
    (h : HEq S T) : S.metric = T.metric := by
  cases hg
  exact congrArg MaximalStandardCapFlow.metric (eq_of_heq h)

private theorem maximal_lifetime_eq_of_heq
    {g0 g1 : StandardInitialMetric} (hg : g0 = g1)
    (S : MaximalStandardCapFlow g0) (T : MaximalStandardCapFlow g1)
    (h : HEq S T) : S.base.lifetime = T.base.lifetime := by
  cases hg
  exact congrArg (fun F => F.base.lifetime) (eq_of_heq h)

namespace CapPersistenceCounterexample

variable {constants : MetricSurgeryConstants} {setup : SurgeryControlSetup constants}
  {start rNext A eta theta cutoff : ℝ}

/-- The actual observation decoration has the unit model lifetime
required by the frozen family comparison. Source: Proposition 16.5,
pp. 370-371; M44 derivation 111. -/
theorem observation_lifetime_one
    (X : CapPersistenceCounterexample.{u} setup start rNext A eta theta cutoff) :
    X.observation.standard_flow.base.lifetime = 1 :=
  (maximal_lifetime_eq_of_heq X.fixed_scales.standard_initial_eq
    X.observation.standard_flow setup.standard_flow X.standard_flow_eq).trans
      setup.standard_lifetime_one

/-- M35 identifies the actual observation metric at each meaningful
standard time; its own connection record is retained. Source:
Corollary 16.9, p. 373; M44 derivation 111. -/
theorem observation_metric_eq
    (X : CapPersistenceCounterexample.{u} setup start rNext A eta theta cutoff)
    (standard : RepairedStandardCapExistenceData setup.standard_initial)
    (unique : RepairedStandardCapUniquenessData setup.standard_initial standard)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    X.observation.standard_flow.metric t = standard.flow.metric t :=
  (congrFun (maximal_metric_eq_of_heq X.fixed_scales.standard_initial_eq
    X.observation.standard_flow setup.standard_flow X.standard_flow_eq) t).trans
      (unique.model_metric_eq setup.standard_flow ht).symm

end CapPersistenceCounterexample

end PoincareMT.M44
