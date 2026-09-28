import PoincareConjecture.Proofs.M47.SeedLimitPhysicalCapture
import PoincareConjecture.Proofs.M47.SeedLimitPhysicalTangent
import PoincareConjecture.Proofs.M47.SeedLimitPhysicalTest
import PoincareConjecture.Proofs.M47.SeedBufferedClock
import PoincareConjecture.Proofs.M47.BlowupControlsSequence
import PoincareConjecture.Proofs.M47.LimitNoncollapseTestParameters
import PoincareConjecture.Proofs.M47.LimitNoncollapseUniformCurvature
import PoincareConjecture.Proofs.M47.LimitNoncollapsePhysicalTime

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47

variable (F : ℕ → SurgeryFlowData.{u}) (W : ∀ k, M33RegularHistoryWindow (F k))
  (history : ∀ k, M33RegularHistoryData (W k)) (baseTime : ℕ → ℝ)
  (hbaseTime : ∀ k, baseTime k ∈ (history k).generalized.interval)
  (basePoint : ∀ k, ((history k).generalized.slice (baseTime k)).carrier)
  (hPositive : ∀ k, 0 < ((F k).connection (baseTime k)).scalarCurvature
    ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k)))
  (hDiverges : Tendsto (fun k => ((F k).connection (baseTime k)).scalarCurvature
    ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k))) atTop atTop)

local notation "V" => regularHistoryBlowupSequence F W history baseTime hbaseTime
  basePoint hPositive hDiverges

variable {H : ℝ≥0∞} (G : GeneralizedBlowupConvergence
  (regularHistoryBlowupSequence F W history baseTime hbaseTime basePoint hPositive hDiverges)
  (blowupBackwardInterval H))

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : MeasurableSpace G.limit.carrier.carrier :=
  G.limit.carrier.measurableSpace
private local instance : BorelSpace G.limit.carrier.carrier := G.limit.carrier.borelSpace
private local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold
private local instance : T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space
private local instance : SecondCountableTopology G.limit.carrier.carrier :=
  G.limit.carrier.secondCountable
private local instance : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace

theorem seedLimit_contracted_physical_test_volume
    (P : M47Predecessors.{u}) {a w epsilon kappa : ℝ}
    (hw : 0 < w) (hepsilon : 0 < epsilon)
    (hbase : ∀ k, a ≤ baseTime k)
    (hcutoff : ∀ k, epsilon ≤ (F k).parameters.epsilon)
    (hvolume : ∀ᶠ k in atTop,
      SurgeryVolumeControlOn (F k) (Icc (a - w) (baseTime k)) kappa (fun _ _ => True))
    (t : ℝ) (ht : t ∈ blowupBackwardInterval H) (p : G.limit.carrier.carrier)
    {r rho R lambda : ℝ} (hr : 0 < r) (hrho : 0 < rho) (hsmall : rho < r)
    (hR : 0 < R) (hRr : R < r) (hlambda : 0 < lambda) (hlambda_lt : lambda < 1)
    (hbuffer : rho / lambda < R)
    (htime : Ioc (t - r ^ 2) t ⊆ blowupBackwardInterval H)
    (hcurv : ∀ s ∈ Ioc (t - r ^ 2) t, ∀ x ∈ (G.limit.flow.metric t).ball p r,
      |(G.limit.flow.connection s).curvatureTensorNorm x| ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal (kappa * lambda ^ 3 * rho ^ 3) ≤
      calibratedMetricVolume (G.limit.flow.metric t) ((G.limit.flow.metric t).ball p r) := by
  classical
  let g := G.limit.flow.metric t
  let Ktime := Icc (t - rho ^ 2) t
  let Kspace := closure (g.ball p R)
  have hKtime : IsCompact Ktime := isCompact_Icc
  have hsub : Ktime ⊆ Ioc (t - r ^ 2) t :=
    limitNoncollapse_shrunk_closed_time_subset hrho hsmall
  have hKJ : Ktime ⊆ blowupBackwardInterval H := hsub.trans htime
  have htop : t ∈ Ktime := ⟨sub_le_self _ (sq_nonneg rho), le_rfl⟩
  have hbottom : t - rho ^ 2 ∈ Ktime := ⟨le_rfl, sub_le_self _ (sq_nonneg rho)⟩
  have hKspace : IsCompact Kspace :=
    PoincareConjecture.Proofs.M09.isCompact_closure_metric_ball g (G.limit.complete t ht) p R
  have hspace : Kspace ⊆ g.ball p r := limitNoncollapse_closure_ball_subset g p hr hRr
  have hcaptured : g.ball p (rho / lambda) ⊆ g.ball p R := by
    intro x hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal hbuffer.le)
  obtain ⟨T, hT, _hTH, hKT⟩ :=
    limitNoncollapse_exists_finite_test_horizon ht.1 hrho (hKJ hbottom)
  have hclock := G.subsequence_strictMono.tendsto_atTop.eventually
    (seed_blowup_eventually_clock_in_buffer baseTime (V).scale hw hT.le hbase
      (V).scalar_diverges)
  have hv := G.subsequence_strictMono.tendsto_atTop.eventually hvolume
  have hmetric := seedLimit_eventually_physical_tangent_comparison G F
    (fun k => (history k).history) hKspace t ht hlambda hlambda_lt
  have hthreshold : r⁻¹ ^ 2 < rho⁻¹ ^ 2 := by
    have hinv : r⁻¹ < rho⁻¹ := by
      simpa only [one_div] using (one_div_lt_one_div_of_lt hrho hsmall)
    nlinarith [inv_pos.mpr hr, inv_pos.mpr hrho]
  have hcurvature := limitNoncollapse_generalized_compact_curvature_lt G P hKtime hKJ
    hKspace (B := rho⁻¹ ^ 2) (fun s hs x hx =>
      ((le_abs_self _).trans (hcurv s (hsub hs) x (hspace hx))).trans_lt hthreshold)
  obtain ⟨k, hm, hK, hcut, hclock, hv⟩ :=
    (hmetric.and (hcurvature.and ((limitNoncollapse_eventually_physical_radius G rho
      hepsilon).and (hclock.and hv)))).exists
  let e := G.embedding k
  let Q := (V).scale (G.subsequence k)
  let hs : t ∈ Icc (-G.exhaustion.time k) 0 := hm.2.1
  let ht' := limitNoncollapse_physical_time_mem G k t hs
  let f := limitCanonicalPhysicalChart e (G.exhaustion.space_open k)
    (history (G.subsequence k)).history t hs ht'
  have hQ : 0 < Q := e.scale_pos
  obtain ⟨hcapture, hupper⟩ := seedLimit_physical_chart_capture_and_volume g
    (C := G.limit.sliceCarrier)
    (D := (F (G.subsequence k)).slice (baseTime (G.subsequence k) + t / Q))
    ((F (G.subsequence k)).metric (baseTime (G.subsequence k) + t / Q)) f p
    hQ hR hlambda hbuffer hKspace (by
      rw [limitCanonicalPhysicalChart_source]
      exact hm.1)
    (fun x hx v => (hm.2.2 hs ht' x hx v).1)
    (fun x hx v => (hm.2.2 hs ht' x hx v).2)
  have hballOpen : IsOpen (g.ball p R) := by
    let : PseudoEMetricSpace G.limit.carrier.carrier := g.comparisonPseudoEMetric
    exact isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hballSub : g.ball p R ⊆ G.exhaustion.space k :=
    subset_closure.trans hm.1
  let small := e.restrict hK.1 hballSub
  have hball : ((F (G.subsequence k)).metric
      (baseTime (G.subsequence k) + t / Q)).ball (f p) (rho / Real.sqrt Q) ⊆
      limitRP2PhysicalMap small (history (G.subsequence k)).history t htop ht' ''
        g.ball p R := hcapture.trans (image_mono hcaptured)
  have hphysical : ∀ s (hsk : s ∈ Ktime), ∀ x ∈ g.ball p R,
      ((history (G.subsequence k)).generalized.connection
        (baseTime (G.subsequence k) + s / Q)).curvatureTensorNorm
          (small.forward s hsk x) ≤ (rho / Real.sqrt Q)⁻¹ ^ 2 := by
    intro s hsk x hx
    have hn := (hK.2.2 s hsk (hK.1 hsk) x (subset_closure hx)).le
    have hnonneg : 0 ≤ ((V).flow (G.subsequence k)).curvatureNorm
        (e.pointMap s (hK.1 hsk) x) := Real.sqrt_nonneg _
    have hc := limitNoncollapse_physical_curvature_bound (rho := rho)
      (K := ((V).flow (G.subsequence k)).curvatureNorm (e.pointMap s (hK.1 hsk) x)) hQ
      (by simpa only [abs_of_nonneg hnonneg] using hn)
    have hc' := (le_abs_self _).trans hc
    simpa only [GeneralizedRicciFlowData.curvatureNorm, GeneralizedFlowCylinder.pointMap,
      small, GeneralizedFlowCylinder.restrict, e, regularHistoryBlowupSequence, Q,
      GeneralizedBlowupSequence.scale] using hc'
  have hphysicalTime : baseTime (G.subsequence k) + t / Q ∈
      Icc (a - w) (baseTime (G.subsequence k)) :=
    hclock.2 t ⟨(hKT htop).1.le, (hKT htop).2⟩
  have hlower := seedLimit_volume_of_physical_test (history (G.subsequence k)) small
    ordConnected_Icc hballOpen p t htop ht' (div_pos hrho (Real.sqrt_pos.mpr hQ))
    (hcut.trans (hcutoff (G.subsequence k))) hv hphysicalTime
    (fun s hs => limitNoncollapse_physical_time_range hQ t rho hs) (f p) hball hphysical
  have hnormalized := limitNoncollapse_cancel_physical_volume hQ hlambda hlower hupper
  exact hnormalized.trans (measure_mono
    (fun x hx => hx.trans_le (ENNReal.ofReal_le_ofReal hRr.le)))

end PoincareConjecture.Proofs.M47
