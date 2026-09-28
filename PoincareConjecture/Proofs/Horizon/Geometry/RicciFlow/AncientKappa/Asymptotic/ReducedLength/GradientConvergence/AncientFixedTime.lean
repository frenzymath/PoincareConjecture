import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.AncientBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Extraction.Ancient.LimitRegularity
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.Eventual

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal ENNReal

universe u
namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.secondCountable

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}

theorem tendsto_integral_reducedLengthPullback_partial_sub_sq
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (q : G.limit.carrier.carrier)
    {a : EuclideanSpace ℝ (Fin n)} {r τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ)
    (hchart : Metric.closedBall a (2 * r) ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target)
    {v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hlim : TendstoUniformlyOn
      (fun k x => G.reducedLengthPullback (σ k)
        ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm x) τ) v atTop (Metric.ball a r))
    (i : Fin n) :
    Tendsto (fun k => ∫ x in Metric.ball a (r / 2),
      (fderiv ℝ (fun y => G.reducedLengthPullback (σ k)
        ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm y) τ) x (EuclideanSpace.single i 1) -
        fderiv ℝ v x (EuclideanSpace.single i 1)) ^ 2) atTop (𝓝 0) := by
  have hτpos : 0 < τ := hτ
  have hsmall : Metric.closedBall a r ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hchart
  obtain ⟨L, C, hC, hbounds⟩ :=
    G.exists_eventually_reducedLengthPullback_weak_data_bounds P q hr hτ hchart
  obtain ⟨c, hc, hell⟩ := G.exists_eventually_sourceCoordinateChart_uniform_ellipticity
    q (isCompact_closedBall a r) hsmall hτ
  let φ : ContDiffBump a := ⟨r / 2, 3 * r / 4, by positivity, by linarith⟩
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (φ : _ → ℝ) := φ.contDiff
  obtain ⟨D, hD⟩ := (isCompact_closedBall a r).exists_bound_of_continuousOn
    (hφ.continuous_fderiv (by simp)).continuousOn
  have hφO : tsupport (φ : _ → ℝ) ⊆ Metric.ball a r := by
    rw [φ.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [φ]; linarith)
  have hclosure : closure (Metric.ball a r) = Metric.closedBall a r :=
    closure_ball a hr.ne'
  have hUclosure : closure (Metric.ball a (r / 2)) = Metric.closedBall a (r / 2) :=
    closure_ball a (half_pos hr).ne'
  let : IsFiniteMeasure (volume.restrict (Metric.ball a r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  let : IsFiniteMeasure (volume.restrict (Metric.ball a (r / 2))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  apply Poincare.Analysis.Elliptic.tendsto_integral_partial_sub_sq_of_eventually_weak_divergence
    Metric.isOpen_ball Metric.isOpen_ball
    (by rw [hUclosure]; exact isCompact_closedBall _ _)
    (by rw [hUclosure]; exact Metric.closedBall_subset_ball (by linarith))
    hc hC (le_max_right D 0) hlim
    (((G.tendstoUniformlyOn_sourceCoordinateChart_divergenceCoefficients q
      (isCompact_closedBall a r) hsmall hτ).mono Metric.ball_subset_closedBall).seq_tendstoUniformlyOn
        σ hσ.tendsto_atTop)
    (F := fun k => (S.rescaling (G.subsequence (σ k))).reducedLengthCoordinateFlux
      S.reference τ (G.sourceCoordinateChart (σ k) q))
    (f := fun k => (S.rescaling (G.subsequence (σ k))).reducedLengthCoordinateSource
      S.reference τ (G.sourceCoordinateChart (σ k) q))
    (L := L) ?_ hφ φ.hasCompactSupport hφO (fun _ => φ.nonneg) (fun _ => φ.le_one)
    (fun x hx => φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)) ?_ i
  · filter_upwards [hσ.tendsto_atTop.eventually hbounds, hσ.tendsto_atTop.eventually hell,
      hσ.tendsto_atTop.eventually (eventually_timeWindow_mem_nhds (by norm_num : (-1 : ℝ) < 0))]
      with k hk he hk₀
    obtain ⟨heChart, heiChart⟩ := G.sourceCoordinateChart_smooth (σ k) q
    have hsrc : closure (Metric.ball a r) ⊆ (G.sourceCoordinateChart (σ k) q).source :=
      hclosure ▸ hk.2.1
    have hcompact : IsCompact (closure (Metric.ball a r)) :=
      hclosure ▸ isCompact_closedBall a r
    refine ⟨hk.1, ?_, ?_, hk.2.2.1, hk.2.2.2, ?_, ?_, ?_⟩
    · exact fun l => (S.rescaling (G.subsequence (σ k))).reducedLengthCoordinateFlux_memLp
        P S.reference hτpos (G.sourceCoordinateChart (σ k) q) heChart heiChart
        Metric.isOpen_ball hcompact hsrc l
    · exact (S.rescaling (G.subsequence (σ k))).reducedLengthCoordinateSource_memLp
        P S.reference hτpos (G.sourceCoordinateChart (σ k) q) heChart heiChart
        Metric.isOpen_ball hcompact hsrc
    · exact fun x hx w => he x (Metric.ball_subset_closedBall hx) w
    · intro x _ l
      rw [← G.reducedLengthPullback_coordinates_eq (σ k) q hk₀ τ]
      exact (S.rescaling (G.subsequence (σ k))).reducedLengthCoordinateFlux_eq_neg_sum
        S.reference τ (G.sourceCoordinateChart (σ k) q) x l
    · exact fun ψ hψ hψc hψO hψ0 =>
        (S.rescaling (G.subsequence (σ k))).reducedLength_weak_coordinate_divergence_le
          P S.reference hτpos (G.sourceCoordinateChart (σ k) q) heChart heiChart
          Metric.isOpen_ball hcompact hsrc hψ hψc hψO hψ0
  · intro l x hx
    have hb := (hD x (Metric.ball_subset_closedBall hx)).trans (le_max_left D 0)
    have h := (fderiv ℝ (φ : _ → ℝ) x).le_opNorm (EuclideanSpace.single l 1)
    simpa only [Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one] using
      h.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

theorem tendsto_integral_reducedLengthPullback_partial_sub_sq_of_locallyUniform
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop
        (univ ×ˢ Ioi (0 : ℝ)))
    (q : G.limit.carrier.carrier) {a : EuclideanSpace ℝ (Fin n)} {r τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ)
    (hchart : Metric.closedBall a (2 * r) ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target)
    (i : Fin n) :
    Tendsto (fun k => ∫ x in Metric.ball a (r / 2),
      (fderiv ℝ (fun y => G.reducedLengthPullback (σ k)
        ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm y) τ) x (EuclideanSpace.single i 1) -
        fderiv ℝ (fun y => l ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm y, τ)) x
          (EuclideanSpace.single i 1)) ^ 2) atTop (𝓝 0) := by
  have hsmall : Metric.closedBall a r ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hchart
  let c : EuclideanSpace ℝ (Fin n) → G.limit.carrier.carrier × ℝ :=
    fun x => ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm x, τ)
  have hc : ContinuousOn c (Metric.closedBall a r) :=
    ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm.continuousOn.mono hsmall).prodMk
      continuousOn_const
  have hcompact := (isCompact_closedBall a r).image_of_continuousOn hc
  have hsub : c '' Metric.closedBall a r ⊆
      univ ×ˢ Ioi (0 : ℝ) := by
    rintro z ⟨x, _, rfl⟩
    exact ⟨mem_univ _, hτ⟩
  have hconv := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hcompact).mp
    (hlim.mono hsub)
  apply G.tendsto_integral_reducedLengthPullback_partial_sub_sq P hσ q hr hτ hchart
  exact (hconv.comp c).mono (fun x hx => mem_image_of_mem c (Metric.ball_subset_closedBall hx))

end PoincareConjecture.AncientCompactTimeConvergence
