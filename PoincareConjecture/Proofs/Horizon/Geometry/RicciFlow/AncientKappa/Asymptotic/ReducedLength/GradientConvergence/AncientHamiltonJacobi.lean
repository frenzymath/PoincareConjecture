import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.AncientTimeEquation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.AncientScalar
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.DirectionalLimit


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal ENNReal

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

local instance : (volume : Measure (ℝ × EuclideanSpace ℝ (Fin n))).IsAddHaarMeasure := by
  change ((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin n)))).IsAddHaarMeasure
  infer_instance

theorem ae_limitReducedLength_hamiltonJacobi_coordinates
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop
        (univ ×ˢ Ioi (0 : ℝ)))
    (q : G.limit.carrier.carrier) {a : EuclideanSpace ℝ (Fin n)} {r α β : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hαβ : α ≤ β)
    (hchart : Metric.closedBall a (2 * r) ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target) :
    ∀ᵐ z ∂(volume.restrict (Ioo α β)).prod (volume.restrict (Metric.ball a (r / 2))),
      let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
      let g := G.limit.flow.metric (-z.1)
      let v := fun y => l (e y, z.1)
      2 * deriv (fun τ => l (e z.2, τ)) z.1 +
        fderiv ℝ v z.2 ((g.pullbackCoefficients e z.2).inverse (fderiv ℝ v z.2)) -
        (G.limit.flow.connection (-z.1)).scalarCurvature (e z.2) + l (e z.2, z.1) / z.1 = 0 := by
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  let O := Metric.ball a (r / 2)
  let I := Ioo α β
  let μ := (volume.restrict I).prod (volume.restrict O)
  let v := fun z : ℝ × EuclideanSpace ℝ (Fin n) => l (e z.2, z.1)
  let u := fun k (z : ℝ × EuclideanSpace ℝ (Fin n)) => G.reducedLengthPullback k (e z.2) z.1
  let ρ := fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
    (G.limit.flow.metric (-z.1)).pullbackVolumeDensity e z.2
  let R := fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
    (G.limit.flow.connection (-z.1)).scalarCurvature (e z.2)
  let F := fun z => (R z - G.limitReducedLengthGradientEnergy q l z / ρ z - v z / z.1) / 2
  have hUC : O ⊆ Metric.closedBall a r :=
    (Metric.ball_subset_ball (by linarith : r / 2 ≤ r)).trans Metric.ball_subset_closedBall
  have hsmall : Metric.closedBall a r ⊆ e.source :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hchart
  obtain ⟨η, hη, henergy⟩ := G.exists_subseq_reducedLength_gradient_energy_tendsto_ae
    P hσ l hlim q hr hα hαβ hchart
  have henergy' : ∀ᵐ z ∂μ,
      Tendsto (fun k => G.reducedLengthPullbackGradientEnergy (σ (η k)) q z) atTop
        (𝓝 (G.limitReducedLengthGradientEnergy q l z)) := by
    simpa only [μ, I, O, restrict_Ioo_eq_restrict_Icc] using henergy
  have hidx : Tendsto (fun k => σ (η k)) atTop atTop := hσ.tendsto_atTop.comp hη.tendsto_atTop
  obtain ⟨L, C, hC, hLip⟩ := G.reducedLengthPullback_eventually_lipschitz_on_chart_cylinder
    P q hr hα hαβ hchart
  have hu : ∀ᶠ k in atTop, LipschitzOnWith L (u k) (I ×ˢ O) := by
    filter_upwards [hLip] with k hk
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    simpa only [u, e, Prod.swap, Prod.dist_eq, max_comm] using hk.1.dist_le_mul z.swap
      ⟨hUC hz.2, ⟨hz.1.1.le, hz.1.2.le⟩⟩ w.swap
      ⟨hUC hw.2, ⟨hw.1.1.le, hw.1.2.le⟩⟩
  have hpoint (z) (hz : z ∈ I ×ˢ O) :
      Tendsto (fun k => u (σ (η k)) z) atTop (𝓝 (v z)) :=
    (hlim.tendsto_at (show (e z.2, z.1) ∈ univ ×ˢ Ioi (0 : ℝ)
      from ⟨mem_univ _, hα.trans hz.1.1⟩)).comp hη.tendsto_atTop
  have hv : LipschitzOnWith L v (I ×ˢ O) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    apply le_of_tendsto ((hpoint z hz).dist (hpoint w hw))
    exact (hidx.eventually hu).mono fun k hk => hk.dist_le_mul z hz w hw
  have hub : ∀ᶠ k in atTop, ∀ z ∈ I ×ˢ O, ‖u (σ (η k)) z‖ ≤ C := by
    filter_upwards [hidx.eventually hLip] with k hk z hz
    have hb := hk.2 z.swap ⟨hUC hz.2, ⟨hz.1.1.le, hz.1.2.le⟩⟩
    exact (abs_of_nonneg hb.1).le.trans hb.2
  have hsource := G.eventually_ae_reducedLengthPullback_time_equation
    P hσ l hlim q hr hα hαβ hchart
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsource
  have hall : ∀ᵐ z ∂μ, ∀ k, N ≤ k →
      2 * fderiv ℝ (u k) z (1, 0) +
        G.reducedLengthPullbackGradientEnergy k q z /
          ((S.rescaling (G.subsequence k)).flow.metric (-z.1)).pullbackVolumeDensity
            (G.sourceCoordinateChart k q) z.2 -
        ((S.rescaling (G.subsequence k)).flow.connection (-z.1)).scalarCurvature
          (G.sourceCoordinateChart k q z.2) + u k z / z.1 = 0 := by
    apply ae_all_iff.mpr
    intro k
    by_cases hk : N ≤ k
    · exact (hN k hk).mono fun _ h _ => h
    · exact Eventually.of_forall fun _ h => (hk h).elim
  have hmem : ∀ᵐ z ∂μ, z ∈ I ×ˢ O := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_ball)
  have hdlim : ∀ᵐ z ∂μ,
      Tendsto (fun k => fderiv ℝ (u (σ (η k))) z (1, 0)) atTop (𝓝 (F z)) := by
    filter_upwards [henergy', hall, hmem] with z hzE hzS hz
    have hzpos : 0 < z.1 := hα.trans hz.1.1
    have hρpos : 0 < ρ z := RicciFlow.BackwardCoordinates.density_pos G.limit.flow e
      contMDiffOn_chart_symm contMDiffOn_chart (z := (z.2, z.1)) (hsmall (hUC hz.2))
    have hρ := ((G.tendstoUniformlyOn_sourceCoordinateChart_volumeDensity q
      (isCompact_closedBall a r) hsmall hzpos).tendsto_at (hUC hz.2)).comp hidx
    have hR := (G.tendsto_sourceCoordinateChart_scalarCurvature q z.2 hzpos).comp hidx
    apply (((hR.sub (hzE.div hρ hρpos.ne')).sub ((hpoint z hz).div_const z.1)).div_const 2).congr'
    filter_upwards [hidx.eventually (eventually_ge_atTop N)] with k hk
    have h := hzS (σ (η k)) hk
    simp only [Function.comp_apply, Pi.div_apply]
    linarith only [h]
  let : IsFiniteMeasure (volume.restrict O) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  let ν : Measure (ℝ × EuclideanSpace ℝ (Fin n)) :=
    (volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin n)))
  let : IsFiniteMeasure (ν.restrict (I ×ˢ O)) := by
    dsimp only [ν]
    rw [← Measure.prod_restrict]
    infer_instance
  have hd : (fun z => fderiv ℝ v z (1, 0)) =ᵐ[μ] F := by
    have hdlim' : ∀ᵐ z ∂ν.restrict (I ×ˢ O),
        Tendsto (fun k => fderiv ℝ (u (σ (η k))) z (1, 0)) atTop (𝓝 (F z)) := by
      simpa only [μ, ν, Measure.prod_restrict] using hdlim
    have h := Poincare.Analysis.Elliptic.ae_directional_fderiv_eq_of_bounded_tendsto
      (μ := ν) (isOpen_Ioo.prod Metric.isOpen_ball)
      (hidx.eventually hu) hv hub hpoint (1, 0) hdlim'
    simpa only [μ, ν, Measure.prod_restrict] using h
  have hdt := Poincare.Analysis.Elliptic.ae_time_slice_deriv_eq_fderiv_of_lipschitz
    isOpen_Ioo Metric.isOpen_ball hv
  filter_upwards [hd, hdt, hmem] with z hz hzdt hzin
  have hρpos : 0 < ρ z := RicciFlow.BackwardCoordinates.density_pos G.limit.flow e
    contMDiffOn_chart_symm contMDiffOn_chart (z := (z.2, z.1)) (hsmall (hUC hzin.2))
  change fderiv ℝ v z (1, 0) = (R z - (ρ z * _) / ρ z - v z / z.1) / 2 at hz
  rw [mul_div_cancel_left₀ _ hρpos.ne'] at hz
  change 2 * deriv (fun τ => v (τ, z.2)) z.1 + _ - R z + v z / z.1 = 0
  rw [hzdt]
  linarith

end PoincareConjecture.AncientCompactTimeConvergence
