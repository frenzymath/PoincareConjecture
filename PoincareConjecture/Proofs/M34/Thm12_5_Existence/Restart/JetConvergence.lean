import PoincareConjecture.Proofs.M34.Thm12_5_Existence.Restart.RicciFlow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34.MetricInteriorCoefficientLimit

open SpacetimeBounds SpacetimeBounds.Bootstrap

variable {ginit : RiemannianMetric 3 StandardCapSpace} {Mfamily : ℕ → Type}
  [∀ k, TopologicalSpace (Mfamily k)] [∀ k, ChartedSpace StandardCapSpace (Mfamily k)]
  [∀ k, IsManifold (𝓡 3) ∞ (Mfamily k)]
  {A : MetricFlowApproximation ginit Mfamily}
  (G : MetricInteriorCoefficientLimit A) (Dinit : LeviCivitaData ginit)

theorem closedSpatialJet_tendsto (m : ℕ) {t : ℝ} (ht : t ∈ Ico 0 A.time)
    (x : StandardCapSpace) :
    Tendsto (fun k => iteratedFDeriv ℝ m (A.coefficients (G.subsequence k) t) x)
      atTop (𝓝 (G.closedSpatialJet m (t, x))) := by
  by_cases hzero : t = 0
  · subst t
    rw [G.closedSpatialJet_zero]
    apply tendsto_const_nhds.congr'
    filter_upwards [G.strictMono.tendsto_atTop.eventually
      (A.compact_sources _ (isCompact_singleton (x := x)))] with k hk
    exact (A.spatialJet_zero (G.subsequence k) m (hk (mem_singleton x))).symm
  · have htpos : t ∈ Ioo 0 A.time := ⟨lt_of_le_of_ne ht.1 (Ne.symm hzero), ht.2⟩
    rw [G.closedSpatialJet_of_mem m htpos]
    exact G.spatialJet_tendsto m htpos x

set_option synthInstance.maxHeartbeats 100000 in

theorem closedFiniteSpatialJet_tendsto (m : ℕ) {t : ℝ} (ht : t ∈ Ico 0 A.time)
    (x : StandardCapSpace) :
    Tendsto (fun k => spatialJet m
      (fun p : ℝ × StandardCapSpace => A.coefficients (G.subsequence k) p.1 p.2) (t, x))
      atTop (𝓝 (spatialJet m G.closedCoefficients (t, x))) := by
  apply tendsto_pi_nhds.mpr
  intro j
  exact G.closedSpatialJet_tendsto j ht x

set_option synthInstance.maxHeartbeats 100000 in

theorem metricTwoJet_tendsto (P : RicciFlowCurvatureTheory.{0})
    {t : ℝ} (ht : t ∈ Ico 0 A.time) (x : StandardCapSpace) :
    Tendsto (fun k => metricTwoJet (A.coefficients (G.subsequence k) t) x) atTop
      (𝓝 (metricTwoJet (G.limitMetric Dinit P t).euclideanCoefficients x)) := by
  have h := (twoJetProjection 3).continuous.tendsto
    (spatialJet 2 G.closedCoefficients (t, x)) |>.comp
      (G.closedFiniteSpatialJet_tendsto 2 ht x)
  simpa only [Function.comp_def, twoJetProjection_spatialJet,
    G.limitMetric_coefficients Dinit P t] using h

end PoincareConjecture.M34.MetricInteriorCoefficientLimit
