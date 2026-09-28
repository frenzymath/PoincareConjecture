import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Constants
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.FlowControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.ProductCylinder
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Rescaling.Closed
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.ReducedGeometry.OrdinaryProductSurvival
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.Noncollapse.TerminalRegion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.OrdinaryProductRicciGeometry

private theorem capture_output
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T3Space M] [ConnectedSpace M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    {I : SpacetimeInterval} (F : RicciFlow 3 M I.domain)
    (P : OrdinaryProductRicciGeometry F.metric I)
    (h : IntrinsicGeneralizedRicciEquation P.leafwiseConnection)
    (O : M14OrdinaryProviders.{u} 3)
    (hc : M14OrdinaryCaptureStatement (P.toLGeometry h) O)
    {T a : ℝ} (hT : T ∈ I.domain) (ha : 0 < a)
    (hI : Icc (T - a) T ⊆ I.domain)
    (hcurv : CompleteBoundedCurvatureOn F (Icc (T - a) T)) :
    Nonempty (M14OrdinaryCaptureOutput (P.toLGeometry h) M I
      P.product.productCylinder P.product.productMetric F T a
      (P.ordinaryCapture F h T a hT)) := by
  obtain ⟨out, _⟩ := hc M I P.product.productCylinder P.product.productMetric F T a
    hT ha hI hcurv (P.ordinaryCapture F h T a hT)
  exact ⟨out⟩

end PoincareConjecture.OrdinaryProductRicciGeometry

namespace PoincareConjecture.M22UniversalNoncollapsingPredecessors

variable {d : ℕ} (H : M22UniversalNoncollapsingPredecessors.{u} d)
  {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]



theorem volume_lower_bound_of_terminal_region (K : AncientKappaSolution 3 M)
    (p : M) (r : ℝ) (hr : 0 < r) (hrtime : r ^ 2 ≤ 2)
    (hcurv : ∀ s ∈ Icc (0 - r ^ 2) 0, ∀ q ∈ (K.flow.metric 0).ball p r,
      (K.flow.connection s).curvatureTensorNorm q ≤ r⁻¹ ^ 2)
    (U : Set M) (hU : IsOpen U)
    (hvol : ENNReal.ofReal universalNoncollapseVolume ≤
      calibratedMetricVolume (K.flow.metric (-2)) U)
    (hlength : ∀ q ∈ U,
      reducedLength K.flow 0 p q 2 ≤ universalNoncollapseLength) :
    ENNReal.ofReal ((universalNoncollapseData H.noncollapse_generalized).universal_kappa *
        r ^ 3) ≤ calibratedMetricVolume (K.flow.metric 0) ((K.flow.metric 0).ball p r) := by
  classical
  obtain ⟨P, hP⟩ := H.ordinary_product M closedAncientInterval K.flow
  let G := P.toLGeometry hP
  have hzero : (0 : ℝ) ∈ closedAncientInterval.domain := by
    change (0 : ℝ) ≤ 0
    exact le_rfl
  have hwindow : Icc (0 - 3 : ℝ) 0 ⊆ closedAncientInterval.domain :=
    fun _ hs => hs.2
  have hbounded := H.complete_bounded_on K hwindow
  have hCapture : M14OrdinaryCaptureStatement (P.toLGeometry hP) H.ordinary_windows :=
    H.ordinary_capture (closedAncientInterval.domain × M)
      (fun z => z.1.val) closedAncientInterval (P.toLGeometry hP) H.ordinary_windows
  obtain ⟨out⟩ := P.capture_output (I := closedAncientInterval) (T := 0) (a := 3)
    K.flow hP H.ordinary_windows hCapture hzero
    (by norm_num : (0 : ℝ) < 3) hwindow hbounded
  obtain ⟨hExponential⟩ := H.exponential (closedAncientInterval.domain × M)
    (fun z => z.1.val) closedAncientInterval G
  let e0 := P.product.sliceIdentification ⟨0, hzero⟩
  let x : (G.slices 0).Point := e0 p
  obtain ⟨E⟩ := hExponential.family 0 x.val x.property
  obtain ⟨S⟩ := P.exists_stable_of_capture (I := closedAncientInterval)
    (T := 0) (τmax := 3) (τ := 2) (x := x.val) K.flow hP H.ordinary_windows
    hCapture hExponential hzero (by norm_num : (0 : ℝ) < 3) hwindow hbounded E
    (by norm_num : (0 : ℝ) < 2) (by norm_num)
  let J : SpacetimeInterval :=
    ⟨Icc (0 - r ^ 2) 0, ordConnected_Icc,
      ⟨0 - r ^ 2, ⟨le_rfl, by nlinarith⟩, 0, ⟨by nlinarith, le_rfl⟩,
        by nlinarith [sq_pos_of_pos hr]⟩⟩
  obtain ⟨B⟩ := P.exists_actualBallCylinder (I := closedAncientInterval)
    K.flow 0 hzero p r hr J rfl
    (fun _ hs => hs.2) hcurv
  have hcomplete : MetricComplete (G.slices 0).metricOnPoints :=
    (RiemannianMetric.metricComplete_iff_diffeomorph (K.flow.metric 0)
      (G.slices 0).metricOnPoints e0
      (fun q v w => (P.product.sliceMetric_eq ⟨0, hzero⟩ q v w).symm)).mp
        (K.complete 0 le_rfl)
  have hcompact := (G.slices 0).metricOnPoints.isCompact_closure_ball_of_metricComplete
    hcomplete x r
  have htwo : (0 - 2 : ℝ) ∈ closedAncientInterval.domain := by norm_num [closedAncientInterval]
  let e2 := P.product.sliceIdentification ⟨0 - 2, htwo⟩
  have hvol' : ENNReal.ofReal universalNoncollapseVolume ≤
      calibratedMetricVolume (G.slices (0 - 2)).metricOnPoints (e2 '' U) := by
    have heq := RiemannianMetric.volumeMeasure_image_diffeomorph (K.flow.metric (0 - 2))
      (G.slices (0 - 2)).metricOnPoints e2
      (fun q v w => (P.product.sliceMetric_eq ⟨0 - 2, htwo⟩ q v w).symm) U
    rw [calibratedMetricVolume_eq_volumeMeasure]
    apply le_trans _ (le_of_eq heq.symm)
    simpa only [zero_sub, calibratedMetricVolume_eq_volumeMeasure] using hvol
  have hlength' : ∀ q ∈ e2 '' U,
      reducedLength K.flow 0 (P.pointMap x.val) (P.pointMap q.val) 2 ≤
        universalNoncollapseLength := by
    rintro q ⟨y, hy, rfl⟩
    have hx : P.pointMap x.val = p := by
      change P.pointMap (e0 p).val = p
      rw [P.product.sliceIdentification_eq]
      rfl
    have hy' : P.pointMap (e2 y).val = y := by
      rw [P.product.sliceIdentification_eq]
      rfl
    rw [hx, hy']
    exact hlength y hy
  let C := P.terminalRegionConfiguration (I := closedAncientInterval)
    (T := 0) (τmax := 3) (hT := hzero) (τ := 2)
    (taubar := universalNoncollapseTime) (l₀ := universalNoncollapseLength)
    (V := universalNoncollapseVolume) K.flow hP out x E B S
    (by norm_num) (by norm_num [universalNoncollapseTime]) hrtime htwo hcompact
    (e2 '' U) (e2.toHomeomorph.isOpenMap U hU) hvol' hlength'
  have h := (universalNoncollapseEstimate H.noncollapse_generalized).estimate
    (closedAncientInterval.domain × M) (fun z => z.1.val) closedAncientInterval G
    0 x E r J (ordinaryMetricBallSource (K.flow.metric 0) p r) B C
  change ENNReal.ofReal ((universalNoncollapseEstimate H.noncollapse_generalized).kappa *
    r ^ 3) ≤ calibratedMetricVolume (G.slices 0).metricOnPoints
      ((G.slices 0).metricOnPoints.ball (e0 p) r) at h
  rw [calibratedMetricVolume_eq_volumeMeasure] at h ⊢
  rw [RiemannianMetric.volumeMeasure_ball_diffeomorph (K.flow.metric 0)
    (G.slices 0).metricOnPoints e0
    (fun q v w => (P.product.sliceMetric_eq ⟨0, hzero⟩ q v w).symm)]
  exact h

end PoincareConjecture.M22UniversalNoncollapsingPredecessors
