import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.LimitGradient.AncientSource
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.AncientQuadratic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.EnergyIntegrability
import PoincareConjecture.Proofs.Horizon.Analysis.Asymptotics.IntegralOrder


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

universe u
namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.secondCountable

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}

theorem reducedLengthPullback_limit_coordinate_gradient_bound_ae
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop
        (univ ×ˢ Ioi (0 : ℝ)))
    (q : G.limit.carrier.carrier) {a : EuclideanSpace ℝ (Fin n)} {r τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ)
    (hchart : Metric.closedBall a (2 * r) ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target) :
    let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
    let v := fun x => l (e x, τ)
    let g := G.limit.flow.metric (-τ)
    ∀ᵐ x ∂volume.restrict (Metric.ball a (r / 2)),
      fderiv ℝ v x ((g.pullbackCoefficients e x).inverse (fderiv ℝ v x)) ≤
        3 * v x / τ := by
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  let u := fun k x => G.reducedLengthPullback (σ k) (e x) τ
  let v := fun x => l (e x, τ)
  let g := G.limit.flow.metric (-τ)
  let gk := fun k => (S.rescaling (G.subsequence (σ k))).flow.metric (-τ)
  let ek := fun k => G.sourceCoordinateChart (σ k) q
  let E := fun k x => (gk k).pullbackVolumeDensity (ek k) x *
    fderiv ℝ (u k) x (((gk k).pullbackCoefficients (ek k) x).inverse (fderiv ℝ (u k) x))
  let E₀ := fun x => g.pullbackVolumeDensity e x *
    fderiv ℝ v x ((g.pullbackCoefficients e x).inverse (fderiv ℝ v x))
  let b := fun k x => (gk k).pullbackVolumeDensity (ek k) x * (3 * u k x / τ)
  let c := fun x => g.pullbackVolumeDensity e x * (3 * v x / τ)
  have hsmall : Metric.closedBall a r ⊆ e.source :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hchart
  have hUO : Metric.ball a (r / 2) ⊆ Metric.ball a r :=
    Metric.ball_subset_ball (by linarith)
  have hUC : Metric.ball a (r / 2) ⊆ Metric.closedBall a r :=
    hUO.trans Metric.ball_subset_closedBall
  have hclosure : closure (Metric.ball a (r / 2)) ⊆ Metric.closedBall a r :=
    closure_minimal hUC Metric.isClosed_closedBall
  have hcompact : IsCompact (closure (Metric.ball a (r / 2))) :=
    (isCompact_closedBall a r).of_isClosed_subset isClosed_closure hclosure
  obtain ⟨L, C, hC, hdata⟩ := G.exists_eventually_reducedLengthPullback_weak_data_bounds
    P q hr hτ hchart
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
  have hEi : ∀ᶠ k in atTop, IntegrableOn (E k) (Metric.ball a (r / 2)) := by
    filter_upwards [hσ.tendsto_atTop.eventually hdata] with k hk
    obtain ⟨he, hei⟩ := G.sourceCoordinateChart_smooth (σ k) q
    exact (gk k).integrableOn_coordinate_gradient_energy (ek k) he hei Metric.isOpen_ball
      hcompact (hclosure.trans hk.2.1) (hk.1.mono hUO)
  have hE₀i : IntegrableOn E₀ (Metric.ball a (r / 2)) :=
    g.integrableOn_coordinate_gradient_energy e contMDiffOn_chart_symm contMDiffOn_chart
      Metric.isOpen_ball hcompact (hclosure.trans hsmall) (hv.mono hUO)
  have hEb : ∀ᶠ k in atTop, ∀ᵐ x ∂volume.restrict (Metric.ball a (r / 2)),
      E k x ≤ b k x := by
    filter_upwards [hσ.tendsto_atTop.eventually
      (G.eventually_reducedLengthPullback_weighted_gradient_energy_bound P q
        (isCompact_closedBall a r) hsmall hτ)] with k hk
    filter_upwards [ae_restrict_of_ae hk, ae_restrict_mem measurableSet_ball] with x hx hxs
    exact hx (hUC hxs)
  have hbc : ∀ᵐ x ∂volume.restrict (Metric.ball a (r / 2)),
      Tendsto (fun k => b k x) atTop (𝓝 (c x)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hρ := ((G.tendstoUniformlyOn_sourceCoordinateChart_volumeDensity q
      (isCompact_closedBall a r) hsmall hτ).tendsto_at (hUC hx)).comp hσ.tendsto_atTop
    exact hρ.mul (((hlim.tendsto_at (show (e x, τ) ∈ univ ×ˢ Ioi (0 : ℝ)
      from ⟨mem_univ _, hτ⟩)).const_mul 3).div_const τ)
  have h := Poincare.Analysis.ae_le_of_tendsto_integral_abs_sub hEi hE₀i
    (G.tendsto_integral_reducedLengthPullback_gradient_energy_sub_abs P hσ l hlim
      q hr hτ hchart) hEb hbc
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨(contMDiffOn_chart_symm (n := ∞)).mdifferentiableOn (by simp),
      (contMDiffOn_chart (n := ∞)).mdifferentiableOn (by simp)⟩
  filter_upwards [h, ae_restrict_mem measurableSet_ball] with x hx hxs
  have hρpos := (g.contDiffAt_pullbackVolumeDensity
    (contMDiffOn_chart_symm.contMDiffAt (e.open_source.mem_nhds (hsmall (hUC hxs))))
    (hD.mfderiv_injective (hsmall (hUC hxs)))).2
  exact (mul_le_mul_iff_right₀ hρpos).mp hx

end PoincareConjecture.AncientCompactTimeConvergence
