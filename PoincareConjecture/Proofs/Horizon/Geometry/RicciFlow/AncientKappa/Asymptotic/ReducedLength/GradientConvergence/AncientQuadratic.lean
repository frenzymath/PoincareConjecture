import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.AncientFixedTime
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.Products








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

theorem tendsto_integral_reducedLengthPullback_gradient_energy_sub_abs
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop
        (univ ×ˢ Ioi (0 : ℝ)))
    (q : G.limit.carrier.carrier) {a : EuclideanSpace ℝ (Fin n)} {r τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ)
    (hchart : Metric.closedBall a (2 * r) ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target) :
    let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
    let u := fun k y => G.reducedLengthPullback (σ k) (e y) τ
    let v := fun y => l (e y, τ)
    Tendsto (fun k => ∫ x in Metric.ball a (r / 2),
      |((S.rescaling (G.subsequence (σ k))).flow.metric (-τ)).pullbackVolumeDensity
          (G.sourceCoordinateChart (σ k) q) x *
          fderiv ℝ (u k) x
            ((((S.rescaling (G.subsequence (σ k))).flow.metric (-τ)).pullbackCoefficients
              (G.sourceCoordinateChart (σ k) q) x).inverse (fderiv ℝ (u k) x)) -
        (G.limit.flow.metric (-τ)).pullbackVolumeDensity e x *
          fderiv ℝ v x (((G.limit.flow.metric (-τ)).pullbackCoefficients e x).inverse
            (fderiv ℝ v x))|) atTop (𝓝 0) := by
  dsimp only
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  let u := fun k y => G.reducedLengthPullback (σ k) (e y) τ
  let v := fun y => l (e y, τ)
  let A := fun k x => LeviCivitaData.Dirichlet.divergenceCoefficients
    ((S.rescaling (G.subsequence (σ k))).flow.metric (-τ))
    (G.sourceCoordinateChart (σ k) q) x
  let B := fun x => LeviCivitaData.Dirichlet.divergenceCoefficients
    (G.limit.flow.metric (-τ)) e x
  have hsmall : Metric.closedBall a r ⊆ e.source :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hchart
  have hUO : Metric.ball a (r / 2) ⊆ Metric.ball a r :=
    Metric.ball_subset_ball (by linarith)
  have hUC : Metric.ball a (r / 2) ⊆ Metric.closedBall a r :=
    hUO.trans Metric.ball_subset_closedBall
  obtain ⟨L, C₀, hC₀, hdata⟩ :=
    G.exists_eventually_reducedLengthPullback_weak_data_bounds P q hr hτ hchart
  have hu : ∀ᶠ k in atTop, LipschitzOnWith L (u k) (Metric.ball a r) :=
    (hσ.tendsto_atTop.eventually hdata).mono fun k hk => hk.1
  have hv : LipschitzOnWith L v (Metric.ball a r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    apply le_of_tendsto ((hlim.tendsto_at (show (e x, τ) ∈ univ ×ˢ Ioi (0 : ℝ)
      from ⟨mem_univ _, hτ⟩)).dist
      (hlim.tendsto_at (show (e y, τ) ∈ univ ×ˢ Ioi (0 : ℝ) from ⟨mem_univ _, hτ⟩)))
    filter_upwards [hu] with k hk
    exact hk.dist_le_mul x hx y hy
  obtain ⟨C, hC, hcoeff⟩ := G.exists_eventually_sourceCoordinateChart_coefficient_bounds
    q (isCompact_closedBall a r) hsmall hτ
  have hconv :=
    (G.tendstoUniformlyOn_sourceCoordinateChart_divergenceCoefficients
      q (isCompact_closedBall a r) hsmall hτ).seq_tendstoUniformlyOn σ hσ.tendsto_atTop
  have hpoint (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.closedBall a r)
      (i j : Fin n) : Tendsto (fun k => A k x i j) atTop (𝓝 (B x i j)) :=
    ((continuous_apply j).tendsto _).comp
      (((continuous_apply i).tendsto _).comp (hconv.tendsto_at hx))
  have hA : ∀ᶠ k in atTop, ∀ i j, AEStronglyMeasurable (fun x => A k x i j)
      (volume.restrict (Metric.ball a (r / 2))) := by
    filter_upwards [hσ.tendsto_atTop.eventually hdata] with k hk i j
    obtain ⟨he, hei⟩ := G.sourceCoordinateChart_smooth (σ k) q
    exact ((LeviCivitaData.Dirichlet.contDiffOn_divergenceCoefficients
      (G.sourceCoordinateChart (σ k) q) he hei i j).continuousOn.mono
        (hUC.trans hk.2.1)).aestronglyMeasurable measurableSet_ball
  have hB (i j : Fin n) : AEStronglyMeasurable (fun x => B x i j)
      (volume.restrict (Metric.ball a (r / 2))) :=
    ((LeviCivitaData.Dirichlet.contDiffOn_divergenceCoefficients e
      contMDiffOn_chart_symm contMDiffOn_chart i j).continuousOn.mono
        (hUC.trans hsmall)).aestronglyMeasurable measurableSet_ball
  have hAb : ∀ᶠ k in atTop, ∀ i j, ∀ᵐ x ∂volume.restrict (Metric.ball a (r / 2)),
      |A k x i j| ≤ C := by
    filter_upwards [hσ.tendsto_atTop.eventually hcoeff] with k hk i j
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (hk x (hUC hx)).2 i j
  have hBb (i j : Fin n) : ∀ᵐ x ∂volume.restrict (Metric.ball a (r / 2)),
      |B x i j| ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    apply le_of_tendsto (hpoint x (hUC hx) i j).abs
    filter_upwards [hσ.tendsto_atTop.eventually hcoeff] with k hk
    exact (hk x (hUC hx)).2 i j
  have hAlim (i j : Fin n) : ∀ᵐ x ∂volume.restrict (Metric.ball a (r / 2)),
      Tendsto (fun k => A k x i j) atTop (𝓝 (B x i j)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hpoint x (hUC hx) i j
  let : IsFiniteMeasure (volume.restrict (Metric.ball a (r / 2))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have h := Poincare.Analysis.Elliptic.tendsto_integral_abs_gradient_quadratic_sub
    Metric.isOpen_ball Metric.isOpen_ball hUO hu hv hA hB hAb hBb hAlim
    (fun i => G.tendsto_integral_reducedLengthPullback_partial_sub_sq_of_locallyUniform
      P hσ l hlim q hr hτ hchart i)
  simpa only [A, B, LeviCivitaData.Dirichlet.sum_divergenceCoefficients_eq_inverse_pairing]
    using h

end PoincareConjecture.AncientCompactTimeConvergence
