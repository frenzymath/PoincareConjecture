import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.EmbeddingConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

open Set Filter Metric
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.NormalizedKappaSolutionSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance terminalConvergenceCarrierConnected (C : FlowCarrier.{0} 3) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

variable {κ : ℝ} (S : NormalizedKappaSolutionSequence κ)
  (G : AncientPointedGeometricConvergence (fun k => (S.term k).carrier)
    (fun k t => (S.term k).flow.flow.metric (t - 1)) (fun k => (S.term k).base) 1)
  (F : RicciFlow 3 G.limitCarrier.carrier (Iic 0))
  (hF : ∀ t : ℝ, t < 0 → F.metric t = G.limitFlow.metric (t + 1))

include hF

theorem terminal_embedding_coefficients_eqOn_actualFlow
    (q : G.limitCarrier.carrier) {x₀ : EuclideanSpace ℝ (Fin 3)} {ρ : ℝ}
    (hchart : closedBall x₀ ρ ⊆ (extChartAt (𝓡 3) q).target)
    (B : ℝ × EuclideanSpace ℝ (Fin 3) → SpacetimeBounds.MetricCoefficient 3)
    (hB : ContDiffOn ℝ ∞ B (Iic 0 ×ˢ closedBall x₀ ρ))
    (hzero : ∀ K, IsCompact K → K ⊆ Iic 0 ×ˢ closedBall x₀ ρ →
      TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ 0
          (fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
            ((S.term (G.subsequence k)).flow.flow.metric z.1).pullbackCoefficients
              (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) z.2)
          (Iic 0 ×ˢ closedBall x₀ ρ))
        (iteratedFDerivWithin ℝ 0 B (Iic 0 ×ˢ closedBall x₀ ρ)) atTop K) :
    EqOn B (fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
      (F.metric z.1).pullbackCoefficients (extChartAt (𝓡 3) q).symm z.2)
      (Iic 0 ×ˢ closedBall x₀ ρ) := by
  let A := fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
    (F.metric z.1).pullbackCoefficients (extChartAt (𝓡 3) q).symm z.2
  have hA : ContDiffOn ℝ ∞ A (Iic 0 ×ˢ closedBall x₀ ρ) :=
    (F.contDiffOn_pullbackCoefficients_within (isOpen_extChartAt_target q)
      (contMDiffOn_extChartAt_symm (n := ∞) q)).mono (prod_mono subset_rfl hchart)
  have hpast : EqOn B A (Iio 0 ×ˢ closedBall x₀ ρ) := by
    intro z hz
    have hzclosed : z ∈ Iic 0 ×ˢ closedBall x₀ ρ :=
      ⟨le_of_lt (show z.1 < 0 from hz.1), hz.2⟩
    have hclosed := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → ℝ × EuclideanSpace ℝ (Fin 3))).comp_tendstoUniformlyOn
        (hzero {z} isCompact_singleton (singleton_subset_iff.mpr hzclosed))
    have hclosedpoint := hclosed.tendsto_at (mem_singleton z)
    simp only [Function.comp_def, iteratedFDerivWithin_zero_apply] at hclosedpoint
    have hnegative := (S.tendstoUniformlyOn_embedding_bilinear_metricJet_unshifted G q 0
      (K := {z}) isCompact_singleton
      (fun w hw => by rcases mem_singleton_iff.mp hw with rfl; exact hz.1)
      (fun w hw => by rcases mem_singleton_iff.mp hw with rfl; exact hchart hz.2)).tendsto_at
        (mem_singleton z)
    have hvalue := (continuous_eval_const
      (0 : Fin 0 → ℝ × EuclideanSpace ℝ (Fin 3))).continuousAt.tendsto.comp hnegative
    simp only [iteratedFDeriv_zero_apply] at hvalue
    dsimp only [A]
    rw [hF z.1 hz.1]
    exact tendsto_nhds_unique hclosedpoint hvalue
  apply hpast.of_subset_closure hB.continuousOn hA.continuousOn
    (prod_mono (show Iio (0 : ℝ) ⊆ Iic 0 from
      fun t ht => show t ≤ 0 from le_of_lt ht) subset_rfl)
  rw [closure_prod_eq, closure_Iio, isClosed_closedBall.closure_eq]

theorem tendstoUniformlyOn_terminal_bilinearJet_on_closedBall
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))
    (q : G.limitCarrier.carrier) {x₀ : EuclideanSpace ℝ (Fin 3)} {ρ : ℝ} (hρ : 0 < ρ)
    (hchart : closedBall x₀ ρ ⊆ (extChartAt (𝓡 3) q).target) (m : ℕ)
    {K : Set (ℝ × EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (hKU : K ⊆ Iic 0 ×ˢ closedBall x₀ ρ) :
    TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ m
        (fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
          ((S.term (G.subsequence k)).flow.flow.metric z.1).pullbackCoefficients
            (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) z.2)
        (Iic 0 ×ˢ closedBall x₀ ρ))
      (iteratedFDerivWithin ℝ m
        (fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
          (F.metric z.1).pullbackCoefficients (extChartAt (𝓡 3) q).symm z.2)
        (Iic 0 ×ˢ closedBall x₀ ρ)) atTop K := by
  obtain ⟨B, hB, hjets⟩ := S.exists_smooth_terminal_embedding_coefficients
    G P hcontrol hcomplete q hρ hchart
  have hBA := S.terminal_embedding_coefficients_eqOn_actualFlow G F hF q hchart B hB (hjets 0)
  exact (hjets m K hK hKU).congr_right fun z hz =>
    iteratedFDerivWithin_congr hBA (hKU hz) m

omit hF in
private theorem halfspace_eq_closedBall_germ
    {x₀ : EuclideanSpace ℝ (Fin 3)} {ρ : ℝ}
    {z : ℝ × EuclideanSpace ℝ (Fin 3)} (hz : z.2 ∈ ball x₀ ρ) :
    Iic (0 : ℝ) ×ˢ closedBall x₀ ρ =ᶠ[𝓝 z]
      Iic 0 ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 3))) := by
  filter_upwards [continuousAt_snd.preimage_mem_nhds (isOpen_ball.mem_nhds hz)] with w hw
  apply propext
  change (w.1 ≤ 0 ∧ w.2 ∈ closedBall x₀ ρ) ↔ (w.1 ≤ 0 ∧ True)
  simp only [ball_subset_closedBall hw, and_true]

theorem tendstoUniformlyOn_terminal_metricJet_on_ball
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))
    (q : G.limitCarrier.carrier) {x₀ : EuclideanSpace ℝ (Fin 3)} {ρ : ℝ} (hρ : 0 < ρ)
    (hchart : closedBall x₀ ρ ⊆ (extChartAt (𝓡 3) q).target)
    (m : ℕ) (a b : Fin 3)
    {K : Set (ℝ × EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (hKU : K ⊆ Iic 0 ×ˢ ball x₀ ρ) :
    TendstoUniformlyOn
      (fun k => M23TerminalMetricJet m (G.limitCarrier.coordinateCoefficient q
        (fun t x v w => spatialPullbackInner G.limitCarrier
          (S.term (G.subsequence k)).carrier ((S.term (G.subsequence k)).flow.flow.metric t)
          (G.embedding k) x v w) a b))
      (M23TerminalMetricJet m (G.limitCarrier.coordinateCoefficient q
        (fun t x v w => (F.metric t).inner x v w) a b)) atTop K := by
  let c := extChartAt (𝓡 3) q
  let Ω : Set (ℝ × EuclideanSpace ℝ (Fin 3)) := Iic 0 ×ˢ closedBall x₀ ρ
  let Γ : Set (ℝ × EuclideanSpace ℝ (Fin 3)) := Iic 0 ×ˢ univ
  let f := fun k (z : ℝ × EuclideanSpace ℝ (Fin 3)) =>
    ((S.term (G.subsequence k)).flow.flow.metric z.1).pullbackCoefficients
      (G.embedding k ∘ c.symm) z.2
  let A := fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
    (F.metric z.1).pullbackCoefficients c.symm z.2
  let fs := fun k => G.limitCarrier.coordinateCoefficient q
    (fun t x v w => spatialPullbackInner G.limitCarrier
      (S.term (G.subsequence k)).carrier ((S.term (G.subsequence k)).flow.flow.metric t)
      (G.embedding k) x v w) a b
  let As := G.limitCarrier.coordinateCoefficient q
    (fun t x v w => (F.metric t).inner x v w) a b
  have hKΩ : K ⊆ Ω := hKU.trans (prod_mono subset_rfl ball_subset_closedBall)
  have hconvex : Convex ℝ Ω := (convex_Iic 0).prod (convex_closedBall x₀ ρ)
  have hne : (interior Ω).Nonempty := by
    rw [show Ω = Iic 0 ×ˢ closedBall x₀ ρ from rfl,
      interior_prod_eq, interior_Iic, interior_closedBall x₀ hρ.ne']
    exact ⟨(-1, x₀), by simp [hρ]⟩
  have hunique := uniqueDiffOn_convex hconvex hne
  have hm : (m : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr (le_top : (m : ℕ∞) ≤ ⊤)
  have hA : ContDiffOn ℝ ∞ A Ω :=
    (F.contDiffOn_pullbackCoefficients_within (isOpen_extChartAt_target q)
      (contMDiffOn_extChartAt_symm (n := ∞) q)).mono (prod_mono subset_rfl hchart)
  have hlimit : TendstoUniformlyOn (fun k => iteratedFDerivWithin ℝ m (f k) Ω)
      (iteratedFDerivWithin ℝ m A Ω) atTop K :=
    S.tendstoUniformlyOn_terminal_bilinearJet_on_closedBall G F hF
      P hcontrol hcomplete q hρ hchart m hK hKΩ
  let L := ContinuousLinearMap.compContinuousMultilinearMapL ℝ
    (fun _ : Fin m => ℝ × EuclideanSpace ℝ (Fin 3))
    (SpacetimeBounds.MetricCoefficient 3) ℝ (coefficientEval a b)
  have hscalar := L.uniformContinuous.comp_tendstoUniformlyOn hlimit
  have hAs : As = coefficientEval a b ∘ A := rfl
  have hc : ContinuousOn c.symm (closedBall x₀ ρ) :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hchart
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
    ((isCompact_closedBall x₀ ρ).image_of_continuousOn hc)
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  have hsource : ∀ᶠ k : ℕ in atTop, EqOn (fs k) (coefficientEval a b ∘ f k) Ω := by
    filter_upwards [eventually_ge_atTop j] with k hk z hz
    convert! S.embedding_coordinateCoefficient_eq_pullbackCoefficients_unshifted
      G q k z.1 z.2 (hchart hz.2) (hmono hk (hj (mem_image_of_mem _ hz.2))) a b using 1
  have hscalarΩ : TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ m (fs k) Ω)
      (iteratedFDerivWithin ℝ m As Ω) atTop K := by
    have htarget : TendstoUniformlyOn
        (fun k => L ∘ iteratedFDerivWithin ℝ m (f k) Ω)
        (iteratedFDerivWithin ℝ m As Ω) atTop K :=
      hscalar.congr_right fun z hz => by
        rw [hAs, (coefficientEval a b).iteratedFDerivWithin_comp_left
          (hA z (hKΩ hz)) hunique (hKΩ hz) hm]
        rfl
    apply htarget.congr
    filter_upwards [hsource, S.eventually_embedding_contDiffOn_terminal G q hchart]
      with k hk hfk z hz
    rw [iteratedFDerivWithin_congr hk (hKΩ hz) m,
      (coefficientEval a b).iteratedFDerivWithin_comp_left (hfk z (hKΩ hz))
        hunique (hKΩ hz) hm]
    rfl
  have htarget := hscalarΩ.congr_right fun z hz =>
    iteratedFDerivWithin_congr_set (halfspace_eq_closedBall_germ (hKU hz).2) m
  apply htarget.congr
  exact Eventually.of_forall fun k z hz =>
    iteratedFDerivWithin_congr_set (halfspace_eq_closedBall_germ (hKU hz).2) m

theorem tendstoUniformlyOn_terminal_metricJet
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))
    (q : G.limitCarrier.carrier) (m : ℕ) (a b : Fin 3)
    {K : Set (ℝ × EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (hKU : K ⊆ Iic 0 ×ˢ (extChartAt (𝓡 3) q).target) :
    TendstoUniformlyOn
      (fun k => M23TerminalMetricJet m (G.limitCarrier.coordinateCoefficient q
        (fun t x v w => spatialPullbackInner G.limitCarrier
          (S.term (G.subsequence k)).carrier ((S.term (G.subsequence k)).flow.flow.metric t)
          (G.embedding k) x v w) a b))
      (M23TerminalMetricJet m (G.limitCarrier.coordinateCoefficient q
        (fun t x v w => (F.metric t).inner x v w) a b)) atTop K := by
  let U : Set (ℝ × EuclideanSpace ℝ (Fin 3)) :=
    Iic 0 ×ˢ (extChartAt (𝓡 3) q).target
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
  apply TendstoLocallyUniformlyOn.mono (s := U) _ hKU
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro z hz
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds hz.2)
  let ρ := R / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hchart : closedBall z.2 ρ ⊆ (extChartAt (𝓡 3) q).target :=
    (closedBall_subset_ball (by dsimp [ρ]; linarith)).trans hRsub
  let C : Set (ℝ × EuclideanSpace ℝ (Fin 3)) := Icc (z.1 - 1) 0 ×ˢ closedBall z.2 (ρ / 2)
  have hC : IsCompact C := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hCsmall : C ⊆ Iic 0 ×ˢ ball z.2 ρ :=
    prod_mono (fun _ ht => ht.2) (closedBall_subset_ball (by linarith))
  have hCnhds : C ∈ 𝓝[U] z := by
    have hnear : Ioi (z.1 - 1) ×ˢ ball z.2 (ρ / 2) ∈ 𝓝 z :=
      (isOpen_Ioi.prod isOpen_ball).mem_nhds ⟨by simp, mem_ball_self (by positivity)⟩
    apply mem_of_superset (inter_mem (mem_nhdsWithin_of_mem_nhds hnear) self_mem_nhdsWithin)
    intro w hw
    exact ⟨⟨hw.1.1.le, hw.2.1⟩, ball_subset_closedBall hw.1.2⟩
  exact ⟨C, hCnhds, S.tendstoUniformlyOn_terminal_metricJet_on_ball G F hF
    P hcontrol hcomplete q hρ hchart m a b hC hCsmall⟩

theorem terminal_pullback_metric_CInfinity
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))
    (q : G.limitCarrier.carrier) (j m : ℕ)
    (K : Set (ℝ × EuclideanSpace ℝ (Fin 3))) (hK : IsCompact K)
    (hKU : K ⊆ {z | z.1 ≤ 0 ∧ z.2 ∈ (extChartAt (𝓡 3) q).target ∧
      (extChartAt (𝓡 3) q).symm z.2 ∈ G.exhaustion j})
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N, ∀ a b : Fin 3, ∀ z ∈ K,
      ‖M23TerminalMetricJet m (G.limitCarrier.coordinateCoefficient q
          (fun t x v w => spatialPullbackInner G.limitCarrier
            (S.term (G.subsequence k)).carrier ((S.term (G.subsequence k)).flow.flow.metric t)
            (G.embedding k) x v w) a b) z -
        M23TerminalMetricJet m (G.limitCarrier.coordinateCoefficient q
          (fun t x v w => (F.metric t).inner x v w) a b) z‖ < ε := by
  have hc (a b : Fin 3) := Metric.tendstoUniformlyOn_iff.mp
    (S.tendstoUniformlyOn_terminal_metricJet G F hF P hcontrol hcomplete q m a b hK
      (fun z hz => ⟨(hKU hz).1, (hKU hz).2.1⟩)) ε hε
  have hall := Filter.eventually_all.mpr (fun a => Filter.eventually_all.mpr (hc a))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hall
  refine ⟨max j N, le_max_left _ _, fun k hk a b z hz => ?_⟩
  have h := hN k ((le_max_right j N).trans hk) a b z hz
  rwa [dist_eq_norm, norm_sub_rev] at h

end PoincareConjecture.NormalizedKappaSolutionSequence
