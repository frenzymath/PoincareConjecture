import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RetainedFinalSourceData
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceFinalChartCapture
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceRawStageMetricPairing
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckCenterLimitCurvature
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckInverseCenterMetric
import PoincareConjecture.Proofs.M28.Mathlib.CanonicalFlowRestriction
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.FixedCoordinateTerminalCoefficients
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.CanonicalImageDistanceLimit












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option synthInstance.maxHeartbeats 200000 in

set_option maxHeartbeats 3200000 in






theorem exists_source_final_chart_distance_limit_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 200 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H),
        epsilon ≤ epsilon0 →
        ∀ (G : RegularPointedMetricConvergence
          (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
          (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))),
        letI := G.limitCarrier.topologicalSpace
        letI := G.limitCarrier.chartedSpace
        letI := G.limitCarrier.isManifold
        letI := G.limitCarrier.t2Space
        ∀ (D0 : LeviCivitaData G.limitMetric) (q : ℕ → G.limitCarrier.carrier)
          (sigma : ℕ → ℕ) (_D : RetainedFinalSourceData H W G D0 q sigma)
          (U : TopologicalSpace.Opens G.limitCarrier.carrier)
          (hfinite : ∀ p q : U, intrinsicEDist G.limitMetric
            (U : Set G.limitCarrier.carrier) (p : G.limitCarrier.carrier)
            (q : G.limitCarrier.carrier) ≠ ⊤)
          (hqU : ∀ i, q i ∈ (U : Set G.limitCarrier.carrier))
          {Y : Set G.limitCarrier.carrier} (Bfront : OpenCylinderModel Y),
          frontier (U : Set G.limitCarrier.carrier) = Bfront.middleSphere →
          Tendsto (fun i => D0.scalarCurvature (q i)) atTop atTop →
          ∀ m : ℝ, 0 < m →
          ∃ eta : ℕ → ℕ, StrictMono eta ∧
          ∃ a : ℝ, ∃ ha : 0 < a, a ≤ m ∧
          let V : TopologicalSpace.Opens E3 := ⟨Metric.ball 0 a, Metric.isOpen_ball⟩
          let K : Set E3 := Metric.closedBall 0 (a / 64)
          let k : K → V := fun z =>
            ⟨z, Metric.closedBall_subset_ball (by linarith) z.property⟩
          letI : Nonempty V := ⟨⟨0, Metric.mem_ball_self ha⟩⟩
          letI := V.isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
          letI := V.isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
          ∃ Fc : RicciFlow 3 V (Icc (-(1 / 8 : ℝ)) 0),
            (∀ s ∈ Icc (-(1 / 8 : ℝ)) 0, ∀ z : V,
              (Fc.connection s).NonnegativeCurvatureOperator z) ∧
            (Fc.connection 0).scalarCurvature ⟨0, Metric.mem_ball_self ha⟩ = 1 ∧
            (∀ v w : E3, (Fc.metric 0).inner ⟨0, Metric.mem_ball_self ha⟩ v w =
              inner ℝ v w) ∧
            letI := intrinsicOpenMetricSpace G.limitMetric U hfinite
            ∃ x : ℕ → K → U,
              (∀ z w : K, (Fc.metric 0).edist (k z) (k w) ≠ ⊤) ∧
              TendstoUniformlyOn
                (fun i (p : K × K) => Real.sqrt (D0.scalarCurvature (q (eta i))) *
                  dist (x i p.1) (x i p.2))
                (fun p => ((Fc.metric 0).edist (k p.1) (k p.2)).toReal) atTop univ ∧
              ∀ᶠ i in atTop, ∀ z : K,
                Real.sqrt (D0.scalarCurvature (q (eta i))) *
                  dist (x i z) ⟨q (eta i), hqU (eta i)⟩ ≤ 3 * a / 64 := by
  classical
  obtain ⟨epsilonN, hNpos, hNsmall, Kcurv, R0, rho, hrho,
      hKcurv, hR0, hRsmall, hrhoR, hnormal⟩ :=
    exists_strongNeck_source_center_limit_accuracy P.local_derivative_estimates
  obtain ⟨epsilonC, hCpos, _hCsmall, hcapture⟩ :=
    exists_source_final_chart_capture_accuracy.{u}
  refine ⟨min epsilonN epsilonC, lt_min hNpos hCpos,
    (min_le_left _ _).trans hNsmall, ?_⟩
  intro epsilon C A E H W hepsilon G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  let := G.limitCarrier.t2Space
  intro D0 q sigma D U hfinite hqU Y Bfront hfront hRdiv m hm
  let nu : ℕ → ℕ := fun i => W.high_index (G.subsequence (sigma (D.column i)))
  let F : ℕ → GeneralizedRicciFlowData.{u} := fun i => (E (nu i + H.shift)).flow
  let t : ℕ → ℝ := fun i => (E (nu i + H.shift)).time
  let Q : ℕ → ℝ := fun i => (F i).scalar ⟨t i, (E (nu i + H.shift)).basepoint⟩
  let Ri : ℕ → ℝ := fun i => D0.scalarCurvature (q i)
  let delta : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 2)
  let e := fun i => H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
    W.high_index G (sigma (D.column i))
  let Hraw : ∀ i, RescaledRawCylinderData (C := (F i).slice (t i))
      (U := strongNeckOpen (D.neck i)) (J := strongNeckBackwardInterval)
      (strongNeckCylinder (D.neck i))
      (GeneralizedStrongNeck.physical_interval_subset (D.neck i)) :=
    fun i => Classical.choice
      (GeneralizedStrongNeck.exists_rescaled_raw_cylinder_flow (D.neck i))
  let Omega : Set E3 := Metric.ball 0 rho
  let hOmega : IsOpen Omega := Metric.isOpen_ball
  let : Nonempty Omega := ⟨⟨0, Metric.mem_ball_self hrho⟩⟩
  obtain ⟨Phi, hPhi, hcurv, hL⟩ :=
    hnormal epsilon (D.neck 0).epsilon_pos
      (hepsilon.trans (min_le_left _ _)) F t D.neck Hraw
  let L := Classical.choice hL
  let eta : ℕ → ℕ := L.subsequence
  have heta : StrictMono eta := L.subsequence_strictMono
  have hnormalization : Tendsto (fun i => (D.neck i).scale⁻¹ ^ 2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop b)] with i hi
    have hbound := D.normalization_lower i
    linarith only [hi, hbound]
  have hread := strongNeck_center_limit_readouts F t D.neck Hraw P hrho hrhoR Phi
    (fun i => (hPhi i).1) (fun i => (hPhi i).2.2.1)
    (fun i => (hPhi i).2.2.2.2.1)
    (fun i => (E (nu i + H.shift)).pinched) hKcurv.le hcurv hnormalization L
  have hchartRead (i : ℕ) :
      (Phi i).source = Metric.ball 0 R0 ∧
        (Phi i).target = ((GeneralizedStrongNeck.rescaled_half_flow
          (D.neck i) (Hraw i)).metric 0).ball (strongNeckSourceCenter (D.neck i)) R0 ∧
        Phi i 0 = strongNeckSourceCenter (D.neck i) :=
    ⟨(hPhi i).1, (hPhi i).2.1, (hPhi i).2.2.1⟩
  obtain ⟨hPsi, hinsideRaw⟩ := hcapture H W
    (hepsilon.trans (min_le_right _ _)) G D0 q sigma D.column D.stage D.neck Hraw
    hR0 hRsmall Phi hchartRead D.scalar_pos D.scale_error D.scalar_error
    D.inverse_center D.core_capture U Bfront hfront hqU hRdiv
  let Psi := fun i => inverseStrongNeckCenterChart (D.neck i) (Phi i) (e i)
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun j => subset_closure.trans (G.exhaustion_step j))
  have hrelative (i : ℕ) : ∀ x ∈ G.exhaustion (D.stage i),
      ∀ v : TangentSpace (𝓡 3) x,
      (1 + delta i)⁻¹ * G.limitMetric.inner x v v ≤
        Q i * ((F i).metric (t i)).inner (e i x)
          (mfderiv (𝓡 3) (𝓡 3) (e i) x v) (mfderiv (𝓡 3) (𝓡 3) (e i) x v) ∧
      Q i * ((F i).metric (t i)).inner (e i x)
          (mfderiv (𝓡 3) (𝓡 3) (e i) x v) (mfderiv (𝓡 3) (𝓡 3) (e i) x v) ≤
        (1 + delta i) * G.limitMetric.inner x v v := by
    apply H.regularRawStageDiffeomorph_relative_inner_bounds W.tube W.radius W.radius_pos
      W.high_index G (sigma (D.column i)) (delta i) (G.exhaustion (D.stage i))
    · exact hmono ((Nat.le_succ _).trans (D.stage_guard i).2)
    · intro x hx v
      exact D.metric_bounds i x (subset_closure hx) v
  let scale : ℕ → ℝ := fun i => Ri i * (Q i * (D.neck i).scale ^ 2)
  let lower : ℕ → ℝ := fun i => scale i / (1 + delta i)
  let upper : ℕ → ℝ := fun i => scale i * (1 + delta i)
  have hrawSqueeze (i : ℕ) : ∀ z ∈ Metric.ball (0 : E3) R0, ∀ v,
      lower i * ((GeneralizedStrongNeck.rescaled_half_flow
        (D.neck i) (Hraw i)).metric 0).pullbackCoefficients (Phi i) z v v ≤
        RiemannianMetric.pullbackCoefficients
          (M13.scaleSmoothMetric G.limitMetric (Ri i) (D.scalar_pos i)) (Psi i) z v v ∧
      RiemannianMetric.pullbackCoefficients
          (M13.scaleSmoothMetric G.limitMetric (Ri i) (D.scalar_pos i)) (Psi i) z v v ≤
        upper i * ((GeneralizedStrongNeck.rescaled_half_flow
        (D.neck i) (Hraw i)).metric 0).pullbackCoefficients (Phi i) z v v :=
    inverseStrongNeckCenterChart_relative_metric (D.neck i) (Hraw i)
      (hepsilon.trans ((min_le_left _ _).trans hNsmall)) hRsmall
      (Phi i) (hPhi i).1 (hPhi i).2.1 (e i) (G.exhaustion (D.stage i))
      (fun y hy hh => ⟨(D.core_capture i y hy hh).1,
        (D.core_capture i y hy hh).2.1⟩)
      G.limitMetric (Q i) (Ri i) (delta i) (D.scalar_pos i)
      (by dsimp only [delta]; positivity) (hrelative i)
  have hdelta : Tendsto delta atTop (𝓝 0) := by
    have hnat : Tendsto (fun i : ℕ => (i : ℝ) + 2) atTop atTop := by
      apply tendsto_atTop.2
      intro b
      filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop b)] with i hi
      linarith
    dsimp only [delta]
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hnat
  have hscale : Tendsto scale atTop (𝓝 1) := by
    apply Metric.tendsto_nhds.2
    intro b hb
    filter_upwards [(tendsto_order.mp hdelta).2 b hb] with i hi
    simpa only [Real.dist_eq] using (D.scale_error i).trans_lt hi
  have hlower : Tendsto lower atTop (𝓝 1) := by
    change Tendsto (scale / (fun i : ℕ => 1 + delta i)) atTop (𝓝 1)
    have hden : Tendsto (fun i : ℕ => 1 + delta i) atTop (𝓝 1) := by
      simpa only [add_zero] using tendsto_const_nhds.add hdelta
    have hquot := hscale.div hden (by norm_num : (1 : ℝ) ≠ 0)
    simpa only [div_one] using hquot
  have hupper : Tendsto upper atTop (𝓝 1) := by
    change Tendsto (fun i : ℕ => scale i * (1 + delta i)) atTop (𝓝 1)
    have hden : Tendsto (fun i : ℕ => 1 + delta i) atTop (𝓝 1) := by
      simpa only [add_zero] using tendsto_const_nhds.add hdelta
    simpa only [Pi.mul_apply, mul_one] using hscale.mul hden
  let a := min (rho / 2) m
  have ha : 0 < a := lt_min (by linarith) hm
  have harho : a < rho := (min_le_left _ _).trans_lt (by linarith)
  have ham : a ≤ m := min_le_right _ _
  have haR : a ≤ R0 := harho.le.trans (by linarith)
  let V : TopologicalSpace.Opens E3 := ⟨Metric.ball 0 a, Metric.isOpen_ball⟩
  let : Nonempty V := ⟨⟨0, Metric.mem_ball_self ha⟩⟩
  let := hOmega.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hOmega.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
  let := V.isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := V.isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
  have hVOmega : (V : Set E3) ⊆ Omega := Metric.ball_subset_ball harho.le
  let Fc := canonicalFlowRestriction V.isOpen hOmega hVOmega L.flow
  have hFcNonnegative : ∀ s ∈ Icc (-(1 / 8 : ℝ)) 0, ∀ z : V,
      (Fc.connection s).NonnegativeCurvatureOperator z := by
    intro s hs z
    exact (canonicalFlowRestriction_nonnegative_iff V.isOpen hOmega hVOmega L.flow s z).2
      (hread.1 s hs ⟨z, hVOmega z.property⟩)
  have hFcScalar : (Fc.connection 0).scalarCurvature ⟨0, Metric.mem_ball_self ha⟩ = 1 := by
    rw [canonicalFlowRestriction_scalar]
    exact hread.2.1
  have hFcOrthonormal : ∀ v w : E3,
      (Fc.metric 0).inner ⟨0, Metric.mem_ball_self ha⟩ v w = inner ℝ v w := by
    intro v w
    rw [canonicalFlowRestriction_inner]
    exact hread.2.2 v w
  let Acoeff : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ := fun z => L.coefficients (0, z)
  let Bcoeff : ℕ → E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ := fun i =>
    ((GeneralizedStrongNeck.rescaled_half_flow
      (D.neck (eta i)) (Hraw (eta i))).metric 0).pullbackCoefficients (Phi (eta i))
  have hcompactSubset : Metric.closedBall (0 : E3) a ⊆ Omega :=
    Metric.closedBall_subset_ball harho
  have hterminal (i : ℕ) (z : E3) (hz : z ∈ Metric.closedBall (0 : E3) a) (v : E3) :
      (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ((GeneralizedStrongNeck.rescaled_eighth_flow
        (D.neck i) (Hraw i)).metric 0).pullbackCoefficients (Phi i) z v v ∧
      ((GeneralizedStrongNeck.rescaled_eighth_flow
        (D.neck i) (Hraw i)).metric 0).pullbackCoefficients (Phi i) z v v ≤
          (9 / 4 : ℝ) * ‖v‖ ^ 2 :=
    (hPhi i).2.2.2.2.2.1 z
      (Metric.closedBall_subset_closedBall (by linarith : a ≤ 2 * rho) hz) v
  have hcoeffLimit : TendstoUniformlyOn Bcoeff Acoeff atTop (V : Set E3) :=
    (L.compact_pullbackCoefficients (fun i => Phi i) (fun _ _ => rfl)
      (by norm_num : (0 : ℝ) ∈ Icc (-(1 / 8 : ℝ)) 0)
      (isCompact_closedBall (0 : E3) a) hcompactSubset).mono Metric.ball_subset_closedBall
  have hAlower : ∀ z ∈ (V : Set E3), ∀ v,
      (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ Acoeff z v v := by
    intro z hz v
    exact (L.compact_coefficient_bounds (fun i => Phi i) (fun _ _ => rfl)
      (by norm_num : (0 : ℝ) ∈ Icc (-(1 / 8 : ℝ)) 0)
      (isCompact_closedBall (0 : E3) a) hcompactSubset hterminal
      z (Metric.ball_subset_closedBall hz) v).1
  have hBbounds : ∀ i z, z ∈ (V : Set E3) → ∀ v,
      (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ Bcoeff i z v v ∧
        Bcoeff i z v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2 := by
    intro i z hz v
    exact hterminal (eta i) z (Metric.ball_subset_closedBall hz) v
  have hFcCoefficients : ∀ (z : V) v w, (Fc.metric 0).inner z v w = Acoeff z v w := by
    intro z v w
    rw [canonicalFlowRestriction_inner]
    exact L.metric_coefficients 0 (by norm_num) ⟨z, hVOmega z.property⟩ v w
  have hsource : ∀ i, Metric.ball (0 : E3) a ⊆ (Psi (eta i)).source := by
    intro i
    rw [(hPsi (eta i)).1]
    exact Metric.ball_subset_ball haR
  have hinside : ∀ᶠ i in atTop, Psi (eta i) '' Metric.ball (0 : E3) a ⊆
      (U : Set G.limitCarrier.carrier) := by
    filter_upwards [heta.tendsto_atTop.eventually hinsideRaw] with i hi
    exact (image_mono (Metric.ball_subset_ball haR)).trans hi
  let qU : ℕ → U := fun i => ⟨q (eta i), hqU (eta i)⟩
  obtain ⟨x, _hxActual, hdistFinite, hdistLimit, hcenterBound⟩ :=
    exists_canonicalImageMetric_source_distance_limit G.limitMetric U hfinite qU
      (fun i => Ri (eta i)) (fun i => D.scalar_pos (eta i)) ha
      (fun i => Psi (eta i)) hsource (fun i => (hPsi (eta i)).2.1) hinside
      Acoeff Bcoeff hAlower hBbounds hcoeffLimit
      (fun i => lower (eta i)) (fun i => upper (eta i))
      (hlower.comp heta.tendsto_atTop) (hupper.comp heta.tendsto_atTop)
      (Eventually.of_forall fun i z hz v =>
        hrawSqueeze (eta i) z (Metric.ball_subset_ball haR hz) v)
      (Fc.metric 0) hFcCoefficients
  exact ⟨eta, heta, a, ha, ham, Fc, hFcNonnegative, hFcScalar,
    hFcOrthonormal, x, hdistFinite, hdistLimit, hcenterBound⟩

end PoincareConjecture.M28.CounterexampleNeckFamily
