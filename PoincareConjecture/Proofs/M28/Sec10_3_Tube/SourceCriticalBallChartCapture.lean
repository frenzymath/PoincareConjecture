import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallNeckScales
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.ChartBallCapture
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckTerminalBalls










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}




theorem tubeCritical_mem_original_ball (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (A1 : ℝ) (k : ℕ)
    (x y : H.tubeCriticalRegion T A1 k) (r : ℝ)
    (hy : y ∈ (H.tubeCriticalMetric T A1 k).ball x
      (Real.sqrt ((E (k + H.shift)).flow.scalar
        ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩) * r)) :
    y.val.val ∈ ((E (k + H.shift)).flow.metric (E (k + H.shift)).time).ball
      x.val.val r := by
  let Q := (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩
  have h₁ : (H.normalizedSliceMetric k).edist x.val.val y.val.val ≤
      (H.tubeMetric T k).edist x.val y.val := by
    rw [tubeMetric, intrinsicOpenMetric_edist]
    exact RiemannianMetric.edist_le_intrinsicEDist _ _ _ _
  have h₂ : (H.tubeMetric T k).edist x.val y.val ≤
      (H.tubeCriticalMetric T A1 k).edist x y := by
    rw [tubeCriticalMetric, intrinsicOpenMetric_edist]
    exact RiemannianMetric.edist_le_intrinsicEDist _ _ _ _
  have hnormal : y.val.val ∈ (H.normalizedSliceMetric k).ball x.val.val
      (Real.sqrt Q * r) := (h₁.trans h₂).trans_lt hy
  have hball := M13.homothety_ball_image
    ((E (k + H.shift)).flow.metric (E (k + H.shift)).time)
    (H.normalizedSliceMetric k) (Diffeomorph.refl (𝓡 3) _ ∞) Q
    (H.base_scalar_pos k) (M13.identity_metricHomothety _ Q (H.base_scalar_pos k))
    x.val.val r
  have hball' :
      ((E (k + H.shift)).flow.metric (E (k + H.shift)).time).ball x.val.val r =
        (H.normalizedSliceMetric k).ball x.val.val (Real.sqrt Q * r) := by
    simpa using hball
  rwa [← hball'] at hnormal

set_option maxHeartbeats 1600000 in





theorem exists_source_criticalBall_neck_chart_capture_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E)
        (T : ∀ k, SourceTubeData (H.segment k)),
        epsilon ≤ epsilon₀ → ∀ (A1 : ℝ) (hA1 : 0 < A1) (phi : ℕ → ℕ)
          (G : RegularPointedMetricConvergence
            (fun k => H.tubeCriticalMetric T A1 (phi k))
            (fun k => H.tubeCriticalBase T A1 hA1 (phi k))),
          letI := G.limitCarrier.topologicalSpace
          letI := G.limitCarrier.chartedSpace
          letI := G.limitCarrier.isManifold
          let i := fun k => phi (G.subsequence k)
          let Q := fun k => (E (i k + H.shift)).flow.scalar
            ⟨(E (i k + H.shift)).time, (E (i k + H.shift)).basepoint⟩
          ∀ (D₀ : LeviCivitaData G.limitMetric) (q : G.limitCarrier.carrier),
            ∃ J : ∀ k, GeneralizedStrongNeck
                (E (i k + H.shift)).flow (E (i k + H.shift)).time epsilon,
              (∀ k, (J k).center = (G.embedding k q).val.val) ∧
              0 < (D₀.scalarCurvature q)⁻¹ ∧
              Tendsto (fun k => Q k * (J k).scale ^ 2) atTop
                (𝓝 (D₀.scalarCurvature q)⁻¹) ∧
              ∃ r : ℝ, 0 < r ∧
                closedBall (extChartAt (𝓡 3) q q) (2 * r) ⊆
                  (extChartAt (𝓡 3) q).target ∧
                ∀ᶠ k in atTop,
                  (D₀.scalarCurvature q)⁻¹ / 2 ≤ Q k * (J k).scale ^ 2 ∧
                  Q k * (J k).scale ^ 2 ≤ 2 * (D₀.scalarCurvature q)⁻¹ ∧
                  (extChartAt (𝓡 3) q).symm ''
                    closedBall (extChartAt (𝓡 3) q q) (2 * r) ⊆ G.exhaustion k ∧
                  ∀ z ∈ closedBall (extChartAt (𝓡 3) q q) (2 * r),
                    (G.embedding k ((extChartAt (𝓡 3) q).symm z)).val.val ∈
                      ((E (i k + H.shift)).flow.metric (E (i k + H.shift)).time).ball
                        (J k).center ((J k).scale * (epsilon⁻¹ / 16)) := by
  classical
  obtain ⟨epsilon₀, hpos, hsmall, hscales⟩ :=
    exists_source_criticalBall_neck_scale_limits_accuracy P
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H T hepsilon A1 hA1 phi G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  let (k : ℕ) : PreconnectedSpace (H.tubeCriticalRegion T A1 (phi k)) :=
    (H.tubeCriticalRegion_connected T A1 hA1 (phi k)).toPreconnectedSpace
  let i := fun k => phi (G.subsequence k)
  let Q := fun k => (E (i k + H.shift)).flow.scalar
    ⟨(E (i k + H.shift)).time, (E (i k + H.shift)).basepoint⟩
  dsimp only
  intro D₀ q
  obtain ⟨J, hcenter, ha, hconv, hbounds⟩ :=
    hscales H T hepsilon A1 hA1 phi G D₀ q
  let a := (D₀.scalarCurvature q)⁻¹
  have heps : 0 < epsilon := (J 0).epsilon_pos
  let rho := Real.sqrt (a / 2) * (epsilon⁻¹ / 16)
  have hrho : 0 < rho := mul_pos (Real.sqrt_pos.mpr (half_pos ha)) (by positivity)
  obtain ⟨r, hr, htarget, hcapture⟩ := G.exists_eventual_chart_ball_capture q rho hrho
  refine ⟨J, hcenter, ha, hconv, r, hr, htarget, ?_⟩
  filter_upwards [hbounds, hcapture] with k hk hcap
  refine ⟨hk.1, hk.2, hcap.1, ?_⟩
  intro z hz
  have hQ : 0 < Q k := H.base_scalar_pos (i k)
  have hsqrt : Real.sqrt (a / 2) ≤ Real.sqrt (Q k) * (J k).scale := by
    have hs := Real.sqrt_le_sqrt hk.1
    change Real.sqrt (a / 2) ≤ Real.sqrt (Q k * (J k).scale ^ 2) at hs
    rwa [Real.sqrt_mul hQ.le, Real.sqrt_sq (J k).scale_pos.le] at hs
  have hradius : rho ≤ Real.sqrt (Q k) * ((J k).scale * (epsilon⁻¹ / 16)) := by
    simpa only [rho, mul_assoc] using
      mul_le_mul_of_nonneg_right hsqrt (by positivity : 0 ≤ epsilon⁻¹ / 16)
  rw [hcenter k]
  apply H.tubeCritical_mem_original_ball T A1 (i k) (G.embedding k q)
    (G.embedding k ((extChartAt (𝓡 3) q).symm z)) ((J k).scale * (epsilon⁻¹ / 16))
  exact (hcap.2 z hz).trans_le (ENNReal.ofReal_le_ofReal hradius)

end PoincareConjecture.M28.CounterexampleNeckFamily
