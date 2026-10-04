import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Flow.InitialEndpointEvolution
import PoincareLib.Geometry.Riemannian.Metric.LocalExtension
import PoincareLib.Geometry.RicciFlow.MetricFamily.Coordinates

/-!
# Reconstructing the actual metric and retained connection family

Positive symmetric smooth coefficients give genuine Riemannian metrics
on the original cap space. A dependent metric/connection pair retains
the supplied initial records exactly outside the interior time domain.
Joint smoothness includes time zero (Theorem 12.5, p. 297).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M34.InteriorCoefficientLimit

open SpacetimeBounds

variable {g0 : StandardInitialMetric} {A : CompactCapApproximation g0}
  (G : InteriorCoefficientLimit A)

/-- Every total time slice of the extended coefficient field is symmetric
(Theorem 12.5, p. 297). -/
theorem closedCoefficients_symm (t : ℝ) (x u v : StandardCapSpace) :
    G.closedCoefficients (t, x) u v = G.closedCoefficients (t, x) v u := by
  by_cases ht : t ∈ Ioo 0 A.time
  · simpa only [G.closedCoefficients_of_mem ht] using G.coefficients_symm ht x u v
  · simp only [closedCoefficients, ht, if_false]
    convert! g0.metric.symm x u v

/-- Every total time slice of the extended field is positive definite
(Theorem 12.5, p. 297). -/
theorem closedCoefficients_pos (P : RicciFlowCurvatureTheory.{0})
    (t : ℝ) (x v : StandardCapSpace) (hv : v ≠ 0) :
    0 < G.closedCoefficients (t, x) v v := by
  by_cases ht : t ∈ Ioo 0 A.time
  · simpa only [G.closedCoefficients_of_mem ht] using G.coefficients_pos P ht x v hv
  · simp only [closedCoefficients, ht, if_false]
    convert! g0.metric.pos x v hv

/-- The actual metric and compatible connection, retaining the supplied
pair whenever time is outside the open interior (Theorem 12.5, p. 297). -/
noncomputable def limitMetricConnection (P : RicciFlowCurvatureTheory.{0}) (t : ℝ) :
    Σ g : RiemannianMetric 3 StandardCapSpace, LeviCivitaData g :=
  if t ∈ Ioo 0 A.time then
    let g := RiemannianMetric.ofEuclideanCoefficients
      (fun x => G.closedCoefficients (t, x)) (G.contDiff_closedCoefficients_slice t)
      (G.closedCoefficients_symm t) (G.closedCoefficients_pos P t)
    ⟨g, g.euclideanLeviCivitaData⟩
  else ⟨g0.metric, g0.connection⟩

/-- The total metric representative of the initial-endpoint limit
(Theorem 12.5, p. 297). -/
noncomputable def limitMetric (P : RicciFlowCurvatureTheory.{0}) (t : ℝ) :
    RiemannianMetric 3 StandardCapSpace := (G.limitMetricConnection P t).1

/-- The actual compatible connection retained with the metric family
(Theorem 12.5, p. 297). -/
noncomputable def limitConnection (P : RicciFlowCurvatureTheory.{0}) (t : ℝ) :
    LeviCivitaData (G.limitMetric P t) := (G.limitMetricConnection P t).2

/-- The reconstructed metrics have exactly the extended coefficients at
every total time (Theorem 12.5, p. 297). -/
theorem limitMetric_coefficients (P : RicciFlowCurvatureTheory.{0}) (t : ℝ) :
    (G.limitMetric P t).euclideanCoefficients = fun x => G.closedCoefficients (t, x) := by
  by_cases ht : t ∈ Ioo 0 A.time
  · simp only [limitMetric, limitMetricConnection, ht, if_true]
    rfl
  · simp only [limitMetric, limitMetricConnection, ht, if_false, closedCoefficients]

/-- The initial metric is the supplied record itself (Theorem 12.5, p. 297). -/
theorem limitMetric_zero (P : RicciFlowCurvatureTheory.{0}) :
    G.limitMetric P 0 = g0.metric := by
  simp [limitMetric, limitMetricConnection]

/-- The initial compatible connection is the supplied record itself,
with the metric equality accounted for (Theorem 12.5, p. 297). -/
theorem limitConnection_zero (P : RicciFlowCurvatureTheory.{0}) :
    HEq (G.limitConnection P 0) g0.connection := by
  have hpair : G.limitMetricConnection P 0 = ⟨g0.metric, g0.connection⟩ := by
    simp [limitMetricConnection]
  exact (Sigma.mk.inj_iff.mp hpair).2

/-- The actual metric section is jointly within-smooth on the initial
half-open spacetime slab (Theorem 12.5, p. 297). -/
theorem limitMetric_smooth (P : RicciFlowCurvatureTheory.{0}) :
    RiemannianMetric.IsSmoothFamilyOn (G.limitMetric P) (Ico 0 A.time) := by
  apply RiemannianMetric.isSmoothFamilyOn_of_constant_chart (fun _ _ => rfl)
    (G.limitMetric P) G.closedCoefficients
  · have hmap : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ × StandardCapSpace) ∞
        (fun p : ℝ × StandardCapSpace => (p.1, p.2)) :=
      contMDiff_fst.prodMk_space contMDiff_snd
    exact (G.contDiffOn_closedCoefficients P).contMDiffOn.comp hmap.contMDiffOn
      (fun _ hp => hp)
  · intro t _ht x u v
    exact congrArg (fun B => B x u v) (G.limitMetric_coefficients P t)

end PoincareMT.M34.InteriorCoefficientLimit
