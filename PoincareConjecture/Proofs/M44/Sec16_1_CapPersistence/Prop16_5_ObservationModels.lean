import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Prop16_5_PreparedCounterexamples
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_9_StandardIdentification

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M44

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

theorem observation_lifetime_one
    (X : CapPersistenceCounterexample.{u} setup start rNext A eta theta cutoff) :
    X.observation.standard_flow.base.lifetime = 1 :=
  (maximal_lifetime_eq_of_heq X.fixed_scales.standard_initial_eq
    X.observation.standard_flow setup.standard_flow X.standard_flow_eq).trans
      setup.standard_lifetime_one

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

end PoincareConjecture.M44
