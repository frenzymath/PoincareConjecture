import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallBackwardData










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric PoincareConjecture.ChartDistance
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily.CriticalBallBackwardChartData

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}
  {H : CounterexampleNeckFamily E} {T : ∀ k, SourceTubeData (H.segment k)}
  {A1 : ℝ} {hA1 : 0 < A1} {phi : ℕ → ℕ}
  {G : RegularPointedMetricConvergence
    (fun k => H.tubeCriticalMetric T A1 (phi k))
    (fun k => H.tubeCriticalBase T A1 hA1 (phi k))}
  {q : G.limitCarrier.carrier} {a : ℝ}
  (D : CriticalBallBackwardChartData H T A1 hA1 phi G q a)



def sourceIndex (k : ℕ) : ℕ := phi (G.subsequence (k + D.offset))



def domain : Set (EuclideanSpace ℝ (Fin 3)) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  exact ball (extChartAt (𝓡 3) q q) (2 * D.radius)


theorem domain_open : IsOpen D.domain := isOpen_ball



instance domain_nonempty : Nonempty D.domain := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  exact ⟨⟨extChartAt (𝓡 3) q q, mem_ball_self (by linarith [D.radius_pos])⟩⟩



def sourceMap (k : ℕ) : D.domain → H.tubeCriticalRegion T A1 (D.sourceIndex k) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  exact fun x => G.embedding (k + D.offset) ((extChartAt (𝓡 3) q).symm x.val)



theorem sourceMap_localDiffeomorph (k : ℕ) :
    letI := D.domain_open.isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (D.sourceMap k) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  apply G.chart_embedding_localDiffeomorph q (k + D.offset) D.domain D.domain_open
  · exact ball_subset_closedBall.trans D.target
  · exact (image_mono ball_subset_closedBall).trans (D.exhaustion k)



theorem sourceMap_mem_ball (k : ℕ) (x : D.domain) :
    (D.sourceMap k x).val.val ∈
      ((E (D.sourceIndex k + H.shift)).flow.metric
        (E (D.sourceIndex k + H.shift)).time).ball
        (D.neck k).center ((D.neck k).scale * (epsilon⁻¹ / 16)) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  exact D.capture k x.val (ball_subset_closedBall x.property)



theorem sourceMap_mem_neck (k : ℕ) (x : D.domain) :
    (D.sourceMap k x).val.val ∈ (D.neck k).carrier := by
  let N := strongNeck_top (D.neck k) D.epsilon_small
  have hball := D.sourceMap_mem_ball k x
  have hradius : (D.neck k).scale * (epsilon⁻¹ / 16) ≤ N.scale * N.epsilon⁻¹ / 8 := by
    change (D.neck k).scale * (epsilon⁻¹ / 16) ≤ (D.neck k).scale * epsilon⁻¹ / 8
    have hpos := mul_pos (D.neck k).scale_pos (inv_pos.mpr (D.neck k).epsilon_pos)
    linarith
  exact (N.small_ball_subset_middle N.center_on_central_sphere
    (hball.trans_le (ENNReal.ofReal_le_ofReal hradius))).1



def neckMap (k : ℕ) : D.domain → strongNeckOpen (D.neck k) :=
  GeneralizedStrongNeck.captured_chart_map (D.neck k) D.domain
    (fun x => (D.sourceMap k x).val.val) (D.sourceMap_mem_neck k)



theorem neckMap_localDiffeomorph (k : ℕ) :
    letI := D.domain_open.isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (D.neckMap k) :=
  GeneralizedStrongNeck.captured_chart_map_localDiffeomorph (D.neck k)
    D.domain D.domain_open (fun x => (D.sourceMap k x).val.val)
    (H.tubeCritical_chart_original_localDiffeomorph T A1 (D.sourceIndex k)
      D.domain D.domain_open (D.sourceMap k) (D.sourceMap_localDiffeomorph k))
    (D.sourceMap_mem_neck k)



def parametrization (k : ℕ) : EuclideanSpace ℝ (Fin 3) → strongNeckOpen (D.neck k) :=
  chartParametrization (fun _ : Unit => D.domain) (fun _ => D.domain_open)
    (i := ()) (D.neckMap k)



@[simp] theorem parametrization_apply (k : ℕ) (x : D.domain) :
    D.parametrization k x = D.neckMap k x :=
  chartParametrization_apply (fun _ : Unit => D.domain) (fun _ => D.domain_open) _ x



theorem parametrization_smooth (k : ℕ) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (D.parametrization k) D.domain := by
  let := D.domain_open.isOpenEmbedding_subtypeVal.singletonChartedSpace
  exact contMDiffOn_chartParametrization (fun _ : Unit => D.domain) (fun _ => D.domain_open)
    (D.neckMap_localDiffeomorph k).contMDiff

set_option maxHeartbeats 1000000 in



theorem parametrization_invertible (k : ℕ) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ D.domain) : (mfderiv (𝓡 3) (𝓡 3) (D.parametrization k) x).IsInvertible := by
  let := D.domain_open.isOpenEmbedding_subtypeVal.singletonChartedSpace
  have hd := mfderiv_chartParametrization (fun _ : Unit => D.domain)
    (fun _ => D.domain_open) (i := ()) ⟨x, hx⟩
      ((D.neckMap_localDiffeomorph k).contMDiff ⟨x, hx⟩)
  rw [show mfderiv (𝓡 3) (𝓡 3) (D.parametrization k) x =
    mfderiv (𝓡 3) (𝓡 3) (D.neckMap k) ⟨x, hx⟩ from hd]
  exact ⟨(D.neckMap_localDiffeomorph k ⟨x, hx⟩).mfderivToContinuousLinearEquiv
    (by simp), rfl⟩



theorem common_window (k : ℕ) :
    a / 8 ≤ (E (D.sourceIndex k + H.shift)).flow.scalar
      ⟨(E (D.sourceIndex k + H.shift)).time,
        (E (D.sourceIndex k + H.shift)).basepoint⟩ * (D.neck k).scale ^ 2 / 4 := by
  have h := D.scale_lower k
  change a / 2 ≤ (E (D.sourceIndex k + H.shift)).flow.scalar
    ⟨(E (D.sourceIndex k + H.shift)).time,
      (E (D.sourceIndex k + H.shift)).basepoint⟩ * (D.neck k).scale ^ 2 at h
  linarith



def sourceFlow (k : ℕ) : RicciFlow 3 (strongNeckOpen (D.neck k)) (Icc (-(a / 8)) 0) :=
  GeneralizedStrongNeck.global_flow (D.neck k) (D.raw k)
    ((E (D.sourceIndex k + H.shift)).flow.scalar
      ⟨(E (D.sourceIndex k + H.shift)).time, (E (D.sourceIndex k + H.shift)).basepoint⟩)
    (H.base_scalar_pos (D.sourceIndex k)) (a / 8) (by linarith [D.scale_pos])
    (D.common_window k)

set_option maxHeartbeats 1800000 in




theorem terminal_coefficients :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ k, EqOn (((D.sourceFlow k).metric 0).pullbackCoefficients (D.parametrization k))
      ((H.tubeCriticalMetric T A1 (D.sourceIndex k)).pullbackCoefficients
        (G.embedding (k + D.offset) ∘ (extChartAt (𝓡 3) q).symm)) D.domain := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro k z hz
  have ht := H.tubeCritical_global_flow_terminal_coefficients T A1 (D.sourceIndex k)
    D.domain D.domain_open (D.sourceMap k) (D.sourceMap_localDiffeomorph k)
    (D.neck k) (D.raw k) (D.sourceMap_mem_neck k) (a / 8)
    (by linarith [D.scale_pos]) (D.common_window k) hz
  apply ht.trans
  have hnear : chartParametrization (fun _ : Unit => D.domain) (fun _ => D.domain_open)
      (i := ()) (D.sourceMap k) =ᶠ[𝓝 z]
        G.embedding (k + D.offset) ∘ (extChartAt (𝓡 3) q).symm := by
    filter_upwards [D.domain_open.mem_nhds hz] with y hy
    exact chartParametrization_apply (fun _ : Unit => D.domain)
      (fun _ => D.domain_open) (D.sourceMap k) ⟨y, hy⟩
  ext v w
  change (H.tubeCriticalMetric T A1 (D.sourceIndex k)).inner
    (chartParametrization (fun _ : Unit => D.domain) (fun _ => D.domain_open)
      (i := ()) (D.sourceMap k) z)
    (mfderiv (𝓡 3) (𝓡 3)
      (chartParametrization (fun _ : Unit => D.domain) (fun _ => D.domain_open)
        (i := ()) (D.sourceMap k)) z v)
    (mfderiv (𝓡 3) (𝓡 3)
      (chartParametrization (fun _ : Unit => D.domain) (fun _ => D.domain_open)
        (i := ()) (D.sourceMap k)) z w) = _
  rw [hnear.self_of_nhds, hnear.mfderiv_eq]
  rfl

end PoincareConjecture.M28.CounterexampleNeckFamily.CriticalBallBackwardChartData
