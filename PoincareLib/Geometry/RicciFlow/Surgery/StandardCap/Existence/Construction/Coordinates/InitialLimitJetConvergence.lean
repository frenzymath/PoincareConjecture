import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Curvature.InitialRicciFlow

/-!
# Pointwise metric-jet convergence at every included time

At positive times the extracted spatial jets converge. At zero every
sufficiently late approximation has exactly the supplied initial jet.
This gives convergence to the reconstructed metric through its raw
second derivatives, including zero (Theorem 12.5, p. 297).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M34.InteriorCoefficientLimit

open SpacetimeBounds SpacetimeBounds.Bootstrap

variable {g0 : StandardInitialMetric} {A : CompactCapApproximation g0}
  (G : InteriorCoefficientLimit A)

/-- Every spatial jet converges pointwise at all included times,
including the exact initial time (Theorem 12.5, p. 297). -/
theorem closedSpatialJet_tendsto (m : ℕ) {t : ℝ} (ht : t ∈ Ico 0 A.time)
    (x : StandardCapSpace) :
    Tendsto (fun k => iteratedFDeriv ℝ m (A.coefficients (G.subsequence k) t) x)
      atTop (𝓝 (G.closedSpatialJet m (t, x))) := by
  by_cases hzero : t = 0
  · subst t
    rw [G.closedSpatialJet_zero]
    apply tendsto_const_nhds.congr'
    filter_upwards [G.strictMono.tendsto_atTop.eventually
      (eventually_compact_subset_double_source g0 (isCompact_singleton (x := x)))] with k hk
    exact (A.spatialJet_zero (G.subsequence k) m (hk (mem_singleton x))).symm
  · have htpos : t ∈ Ioo 0 A.time := ⟨lt_of_le_of_ne ht.1 (Ne.symm hzero), ht.2⟩
    rw [G.closedSpatialJet_of_mem m htpos]
    exact G.spatialJet_tendsto m htpos x

set_option synthInstance.maxHeartbeats 100000 in
-- The finite jet collects dependent multilinear-map components.
/-- All components of each finite spatial jet converge at the included
initial time as well as in the interior (Theorem 12.5, p. 297). -/
theorem closedFiniteSpatialJet_tendsto (m : ℕ) {t : ℝ} (ht : t ∈ Ico 0 A.time)
    (x : StandardCapSpace) :
    Tendsto (fun k => spatialJet m
      (fun p : ℝ × StandardCapSpace => A.coefficients (G.subsequence k) p.1 p.2) (t, x))
      atTop (𝓝 (spatialJet m G.closedCoefficients (t, x))) := by
  apply tendsto_pi_nhds.mpr
  intro j
  exact G.closedSpatialJet_tendsto j ht x

set_option synthInstance.maxHeartbeats 100000 in
-- Projection converts the finite two-jet to ordinary first and second derivatives.
/-- The raw spatial metric two-jets converge to those of the actual
reconstructed metric at every included time (Theorem 12.5, p. 297). -/
theorem metricTwoJet_tendsto (P : RicciFlowCurvatureTheory.{0})
    {t : ℝ} (ht : t ∈ Ico 0 A.time) (x : StandardCapSpace) :
    Tendsto (fun k => metricTwoJet (A.coefficients (G.subsequence k) t) x) atTop
      (𝓝 (metricTwoJet (G.limitMetric P t).euclideanCoefficients x)) := by
  have h := (twoJetProjection 3).continuous.tendsto
    (spatialJet 2 G.closedCoefficients (t, x)) |>.comp
      (G.closedFiniteSpatialJet_tendsto 2 ht x)
  simpa only [Function.comp_def, twoJetProjection_spatialJet,
    G.limitMetric_coefficients P t] using h

end PoincareMT.M34.InteriorCoefficientLimit
