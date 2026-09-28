import PoincareConjecture.Definitions.Ch11.BlowupLimits

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.GeneralizedBlowupConvergence

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (C : GeneralizedBlowupConvergence S J)

theorem exists_exhaustion_superset {K : Set C.limit.sliceCarrier.carrier}
    (hK : IsCompact K) : ∃ j, K ⊆ C.exhaustion.space j :=
  hK.elim_directed_cover C.exhaustion.space C.exhaustion.space_open
    (fun x _ => C.exhaustion.space_covers.symm ▸ mem_univ x)
    C.exhaustion.space_increasing.directed_le

local instance : TopologicalSpace C.limit.carrier.carrier := C.limit.carrier.topologicalSpace
local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.limit.carrier.carrier :=
  C.limit.carrier.chartedSpace
local instance : IsManifold (𝓡 3) ∞ C.limit.carrier.carrier := C.limit.carrier.isManifold

theorem tendsto_coordinate_metricJetWithin
    (q : C.limit.sliceCarrier.carrier) (r : ℕ) (a b : Fin 3)
    (p : ℝ × EuclideanSpace ℝ (Fin 3))
    (hp : p ∈ blowupMetricChartDomain C.limit q) :
    Tendsto (fun k => iteratedFDerivWithin ℝ r
      (blowupPullbackCoefficient (C.embedding k) q a b)
      (Icc (-C.exhaustion.time k) 0 ×ˢ (extChartAt (𝓡 3) q).target) p)
      atTop (𝓝 (iteratedFDerivWithin ℝ r
        (FlowCarrier.coordinateCoefficient C.limit.carrier q
          (fun t x v w => (C.limit.flow.metric t).inner x v w) a b)
        (blowupMetricChartDomain C.limit q) p)) := by
  obtain ⟨j, hj⟩ := C.exists_exhaustion_superset
    (isCompact_singleton (x := (extChartAt (𝓡 3) q).symm p.2))
  have hdom : {p} ⊆ {z | z ∈ blowupMetricChartDomain C.limit q ∧
      (extChartAt (𝓡 3) q).symm z.2 ∈ C.exhaustion.space j} :=
    singleton_subset_iff.mpr ⟨hp, hj (mem_singleton _)⟩
  apply Metric.tendsto_atTop.mpr
  intro epsilon hepsilon
  obtain ⟨N, _, hN⟩ := C.pullback_metric_CInfinity q j r {p}
    isCompact_singleton hdom epsilon hepsilon
  refine ⟨N, fun k hk => ?_⟩
  simpa only [dist_eq_norm] using (hN k hk).2 a b p (mem_singleton p)

theorem tendsto_coordinate_metricJetWithin_apply
    (q : C.limit.sliceCarrier.carrier) (r : ℕ) (a b : Fin 3)
    (p : ℝ × EuclideanSpace ℝ (Fin 3))
    (hp : p ∈ blowupMetricChartDomain C.limit q)
    (v : Fin r → ℝ × EuclideanSpace ℝ (Fin 3)) :
    Tendsto (fun k => iteratedFDerivWithin ℝ r
      (blowupPullbackCoefficient (C.embedding k) q a b)
      (Icc (-C.exhaustion.time k) 0 ×ˢ (extChartAt (𝓡 3) q).target) p v)
      atTop (𝓝 (iteratedFDerivWithin ℝ r
        (FlowCarrier.coordinateCoefficient C.limit.carrier q
          (fun t x u w => (C.limit.flow.metric t).inner x u w) a b)
        (blowupMetricChartDomain C.limit q) p v)) :=
  (continuous_eval_const v).continuousAt.tendsto.comp
    (C.tendsto_coordinate_metricJetWithin q r a b p hp)

end PoincareConjecture.GeneralizedBlowupConvergence
