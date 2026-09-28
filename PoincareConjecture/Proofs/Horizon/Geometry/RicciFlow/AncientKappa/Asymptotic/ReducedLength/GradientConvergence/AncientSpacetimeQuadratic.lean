import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.AncientQuadratic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.AncientSpacetimeCoefficients
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.ParametricProducts

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

theorem tendsto_iterated_integral_reducedLengthPullback_gradient_energy_sub_abs
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop
        (univ ×ˢ Ioi (0 : ℝ)))
    (q : G.limit.carrier.carrier) {a : EuclideanSpace ℝ (Fin n)} {r α β : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hαβ : α ≤ β)
    (hchart : Metric.closedBall a (2 * r) ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target) :
    let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
    let u := fun k τ y => G.reducedLengthPullback (σ k) (e y) τ
    let v := fun τ y => l (e y, τ)
    Tendsto (fun k => ∫ τ in Icc α β, ∫ x in Metric.ball a (r / 2),
      |((S.rescaling (G.subsequence (σ k))).flow.metric (-τ)).pullbackVolumeDensity
          (G.sourceCoordinateChart (σ k) q) x *
          fderiv ℝ (u k τ) x
            ((((S.rescaling (G.subsequence (σ k))).flow.metric (-τ)).pullbackCoefficients
              (G.sourceCoordinateChart (σ k) q) x).inverse (fderiv ℝ (u k τ) x)) -
        (G.limit.flow.metric (-τ)).pullbackVolumeDensity e x *
          fderiv ℝ (v τ) x (((G.limit.flow.metric (-τ)).pullbackCoefficients e x).inverse
            (fderiv ℝ (v τ) x))|) atTop (𝓝 0) := by
  dsimp only
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  let u := fun k (z : EuclideanSpace ℝ (Fin n) × ℝ) =>
    G.reducedLengthPullback (σ k) (e z.1) z.2
  let v := fun z : EuclideanSpace ℝ (Fin n) × ℝ => l (e z.1, z.2)
  let A := fun k (z : EuclideanSpace ℝ (Fin n) × ℝ) =>
    LeviCivitaData.Dirichlet.divergenceCoefficients
      ((S.rescaling (G.subsequence (σ k))).flow.metric (-z.2))
      (G.sourceCoordinateChart (σ k) q) z.1
  let B := fun z : EuclideanSpace ℝ (Fin n) × ℝ =>
    LeviCivitaData.Dirichlet.divergenceCoefficients (G.limit.flow.metric (-z.2)) e z.1
  have hsmall : Metric.closedBall a r ⊆ e.source :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hchart
  have hUO : Metric.ball a (r / 2) ⊆ Metric.ball a r :=
    Metric.ball_subset_ball (by linarith)
  have hUC : Metric.ball a (r / 2) ⊆ Metric.closedBall a r :=
    hUO.trans Metric.ball_subset_closedBall
  obtain ⟨L, C₀, hC₀, hLip⟩ := G.reducedLengthPullback_eventually_lipschitz_on_chart_cylinder
    P q hr hα hαβ hchart
  have hu : ∀ᶠ k in atTop,
      LipschitzOnWith L (u k) (Metric.ball a r ×ˢ Icc α β) := by
    filter_upwards [hσ.tendsto_atTop.eventually hLip] with k hk
    exact hk.1.mono (Set.prod_mono Metric.ball_subset_closedBall Subset.rfl)
  have hv : LipschitzOnWith L v (Metric.ball a r ×ˢ Icc α β) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    apply le_of_tendsto ((hlim.tendsto_at ⟨mem_univ _, hα.trans_le hz.2.1⟩).dist
      (hlim.tendsto_at ⟨mem_univ _, hα.trans_le hw.2.1⟩))
    filter_upwards [hu] with k hk
    exact hk.dist_le_mul z hz w hw
  obtain ⟨C, hC, hcoeff⟩ := G.exists_eventually_sourceCoordinateChart_spacetime_coefficient_bound
    q (isCompact_closedBall a r) hsmall hα hαβ
  have hconv :=
    (G.tendstoUniformlyOn_sourceCoordinateChart_divergenceCoefficients_spacetime
      q (isCompact_closedBall a r) hsmall hα hαβ).seq_tendstoUniformlyOn σ hσ.tendsto_atTop
  have hAb : ∀ᶠ k in atTop, ∀ z ∈ Metric.ball a (r / 2) ×ˢ Icc α β, ∀ i j,
      |A k z i j| ≤ C := by
    filter_upwards [hσ.tendsto_atTop.eventually hcoeff] with k hk z hz i j
    exact hk z ⟨hUC hz.1, hz.2⟩ i j
  have hBb : ∀ z ∈ Metric.ball a (r / 2) ×ˢ Icc α β, ∀ i j, |B z i j| ≤ C := by
    intro z hz i j
    have hp : Tendsto (fun k => A k z i j) atTop (𝓝 (B z i j)) :=
      ((continuous_apply j).tendsto _).comp
        (((continuous_apply i).tendsto _).comp (hconv.tendsto_at ⟨hUC hz.1, hz.2⟩))
    apply le_of_tendsto hp.abs
    exact hAb.mono fun k hk => hk z hz i j
  have hA : ∀ᶠ k in atTop, ∀ i j,
      AEStronglyMeasurable (fun z : ℝ × EuclideanSpace ℝ (Fin n) => A k z.swap i j)
        ((volume.restrict (Icc α β)).prod (volume.restrict (Metric.ball a (r / 2)))) := by
    filter_upwards [hσ.tendsto_atTop.eventually
      (G.eventually_subset_sourceCoordinateChart q (isCompact_closedBall a r) hsmall)] with k hk i j
    obtain ⟨he, hei⟩ := G.sourceCoordinateChart_smooth (σ k) q
    have hdom : Metric.ball a (r / 2) ×ˢ Icc α β ⊆
        RicciFlow.BackwardCoordinates.domain (Iio 0) (G.sourceCoordinateChart (σ k) q) := by
      intro z hz
      exact ⟨hk (hUC hz.1), by simpa only [interior_Iio, mem_preimage, mem_Iio] using neg_neg_of_pos (hα.trans_le hz.2.1)⟩
    have hc := (RicciFlow.BackwardCoordinates.contDiffOn_weightedPrincipal
      (S.rescaling (G.subsequence (σ k))).flow (G.sourceCoordinateChart (σ k) q)
      he hei i j).continuousOn.mono hdom
    rw [Measure.prod_restrict]
    exact (hc.comp continuous_swap.continuousOn (fun z hz => ⟨hz.2, hz.1⟩)).aestronglyMeasurable
      (measurableSet_Icc.prod measurableSet_ball)
  have hB (i j : Fin n) :
      AEStronglyMeasurable (fun z : ℝ × EuclideanSpace ℝ (Fin n) => B z.swap i j)
        ((volume.restrict (Icc α β)).prod (volume.restrict (Metric.ball a (r / 2)))) := by
    have hdom : Metric.ball a (r / 2) ×ˢ Icc α β ⊆
        RicciFlow.BackwardCoordinates.domain (Iio 0) e := by
      intro z hz
      exact ⟨hsmall (hUC hz.1), by simpa only [interior_Iio, mem_preimage, mem_Iio] using neg_neg_of_pos (hα.trans_le hz.2.1)⟩
    have hc := (RicciFlow.BackwardCoordinates.contDiffOn_weightedPrincipal G.limit.flow e
      contMDiffOn_chart_symm contMDiffOn_chart i j).continuousOn.mono hdom
    rw [Measure.prod_restrict]
    exact (hc.comp continuous_swap.continuousOn (fun z hz => ⟨hz.2, hz.1⟩)).aestronglyMeasurable
      (measurableSet_Icc.prod measurableSet_ball)
  let : IsFiniteMeasure (volume.restrict (Metric.ball a (r / 2))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have h := Poincare.Analysis.Elliptic.tendsto_iterated_integral_abs_gradient_quadratic_sub
    Metric.isOpen_ball measurableSet_ball hUO measurableSet_Icc hu hv hC hA hB hAb hBb
    (fun τ hτ => by
      simpa only [A, B, LeviCivitaData.Dirichlet.sum_divergenceCoefficients_eq_inverse_pairing]
        using G.tendsto_integral_reducedLengthPullback_gradient_energy_sub_abs
          P hσ l hlim q hr (hα.trans_le hτ.1) hchart)
  simpa only [A, B, LeviCivitaData.Dirichlet.sum_divergenceCoefficients_eq_inverse_pairing]
    using h

end PoincareConjecture.AncientCompactTimeConvergence
