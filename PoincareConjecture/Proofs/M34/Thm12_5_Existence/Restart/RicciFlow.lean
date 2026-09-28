import PoincareConjecture.Proofs.M34.Thm12_5_Existence.Restart.MetricFamily
import PoincareConjecture.Proofs.M34.Standard.RicciOperatorEvaluation

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

set_option synthInstance.maxHeartbeats 100000 in

theorem limitMetric_equation (P : RicciFlowCurvatureTheory.{0})
    {t : ℝ} (ht : t ∈ Ico 0 A.time) (x u v : StandardCapSpace) :
    HasDerivWithinAt (fun s => (G.limitMetric Dinit P s).inner x u v)
      (-2 * (G.limitConnection Dinit P t).ricci x u v) (Ico 0 A.time) t := by
  have h := ((G.hasDerivWithinAt_closedCoefficients P ht x).clm_apply
    (hasDerivWithinAt_const t (Ico 0 A.time) u)).clm_apply
      (hasDerivWithinAt_const t (Ico 0 A.time) v)
  have hop : jetRicciFlowOperator 3 (spatialJet 2 G.closedCoefficients (t, x)) u v =
      -2 * (G.limitConnection Dinit P t).ricci x u v := by
    rw [jetRicciFlowOperator, Function.comp_apply, twoJetProjection_spatialJet,
      ← G.limitMetric_coefficients Dinit P t]
    exact ricciFlowOperator_metricTwoJet_apply (G.limitConnection Dinit P t) x u v
  have hfunction : (fun s => (G.limitMetric Dinit P s).inner x u v) =
      (fun s => G.closedCoefficients (s, x) u v) :=
    funext (fun s => congrArg (fun B => B x u v) (G.limitMetric_coefficients Dinit P s))
  rw [hfunction]
  simpa only [map_zero, add_zero, zero_add, hop] using h

noncomputable def initialFlow (P : RicciFlowCurvatureTheory.{0}) :
    RicciFlow 3 StandardCapSpace (Ico 0 A.time) where
  metric := G.limitMetric Dinit P
  connection := G.limitConnection Dinit P
  interval := ordConnected_Ico
  nontrivial := ⟨0, ⟨le_rfl, A.time_pos⟩, A.time / 2,
    ⟨(half_pos A.time_pos).le, half_lt_self A.time_pos⟩, (half_pos A.time_pos).ne⟩
  smooth := G.limitMetric_smooth Dinit P
  equation t ht x u v := G.limitMetric_equation Dinit P (t := t) ht x u v

theorem initialFlow_metric_zero (P : RicciFlowCurvatureTheory.{0}) :
    (G.initialFlow Dinit P).metric 0 = ginit := G.limitMetric_zero Dinit P

theorem initialFlow_connection_zero (P : RicciFlowCurvatureTheory.{0}) :
    HEq ((G.initialFlow Dinit P).connection 0) Dinit := G.limitConnection_zero Dinit P

end PoincareConjecture.M34.MetricInteriorCoefficientLimit
