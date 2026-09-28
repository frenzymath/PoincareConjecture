import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.AncientSpacetimeQuadratic
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.EnergyLp
import PoincareConjecture.Proofs.Horizon.Analysis.Asymptotics.IntegralOrder

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

def reducedLengthPullbackGradientEnergy (G : AncientCompactTimeConvergence S)
    (k : ℕ) (q : G.limit.carrier.carrier) (z : ℝ × EuclideanSpace ℝ (Fin n)) : ℝ :=
  let e := G.sourceCoordinateChart k q
  let g := (S.rescaling (G.subsequence k)).flow.metric (-z.1)
  let u := fun y => G.reducedLengthPullback k
    ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm y) z.1
  g.pullbackVolumeDensity e z.2 *
    fderiv ℝ u z.2 ((g.pullbackCoefficients e z.2).inverse (fderiv ℝ u z.2))

def limitReducedLengthGradientEnergy (G : AncientCompactTimeConvergence S)
    (q : G.limit.carrier.carrier) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (z : ℝ × EuclideanSpace ℝ (Fin n)) : ℝ :=
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  let g := G.limit.flow.metric (-z.1)
  let u := fun y => l (e y, z.1)
  g.pullbackVolumeDensity e z.2 *
    fderiv ℝ u z.2 ((g.pullbackCoefficients e z.2).inverse (fderiv ℝ u z.2))

theorem reducedLength_gradient_energies_memLp_top
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop
        (univ ×ˢ Ioi (0 : ℝ)))
    (q : G.limit.carrier.carrier) {a : EuclideanSpace ℝ (Fin n)} {r α β : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hαβ : α ≤ β)
    (hchart : Metric.closedBall a (2 * r) ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target) :
    let μ := (volume.restrict (Icc α β)).prod (volume.restrict (Metric.ball a (r / 2)))
    MemLp (G.limitReducedLengthGradientEnergy q l) ∞ μ ∧
      ∀ᶠ k in atTop, MemLp (G.reducedLengthPullbackGradientEnergy k q) ∞ μ := by
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  let u := fun k (z : EuclideanSpace ℝ (Fin n) × ℝ) =>
    G.reducedLengthPullback k (e z.1) z.2
  let v := fun z : EuclideanSpace ℝ (Fin n) × ℝ => l (e z.1, z.2)
  let μ := (volume.restrict (Icc α β)).prod (volume.restrict (Metric.ball a (r / 2)))
  have hsmall : Metric.closedBall a r ⊆ e.source :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hchart
  have hUO : Metric.ball a (r / 2) ⊆ Metric.ball a r := Metric.ball_subset_ball (by linarith)
  have hUC : Metric.ball a (r / 2) ⊆ Metric.closedBall a r := hUO.trans Metric.ball_subset_closedBall
  obtain ⟨L, C₀, hC₀, hLip⟩ := G.reducedLengthPullback_eventually_lipschitz_on_chart_cylinder
    P q hr hα hαβ hchart
  have hu : ∀ᶠ k in atTop, LipschitzOnWith L (u k) (Metric.ball a r ×ˢ Icc α β) :=
    hLip.mono fun k hk => hk.1.mono (Set.prod_mono Metric.ball_subset_closedBall Subset.rfl)
  have hv : LipschitzOnWith L v (Metric.ball a r ×ˢ Icc α β) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    apply le_of_tendsto ((hlim.tendsto_at (show (e z.1, z.2) ∈ univ ×ˢ Ioi (0 : ℝ)
      from ⟨mem_univ _, hα.trans_le hz.2.1⟩)).dist
      (hlim.tendsto_at (show (e w.1, w.2) ∈ univ ×ˢ Ioi (0 : ℝ)
        from ⟨mem_univ _, hα.trans_le hw.2.1⟩)))
    filter_upwards [hσ.tendsto_atTop.eventually hu] with k hk
    exact hk.dist_le_mul z hz w hw
  obtain ⟨C, hC, hcoeff⟩ := G.exists_eventually_sourceCoordinateChart_spacetime_coefficient_bound
    q (isCompact_closedBall a r) hsmall hα hαβ
  have hconv := G.tendstoUniformlyOn_sourceCoordinateChart_divergenceCoefficients_spacetime
    q (isCompact_closedBall a r) hsmall hα hαβ
  have hmem : ∀ᵐ z ∂μ, z ∈ Icc α β ×ˢ Metric.ball a (r / 2) := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_ball)
  have hA : ∀ᶠ k in atTop, ∀ i j, MemLp
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) => LeviCivitaData.Dirichlet.divergenceCoefficients
        ((S.rescaling (G.subsequence k)).flow.metric (-z.1)) (G.sourceCoordinateChart k q) z.2 i j) ∞ μ := by
    filter_upwards [hcoeff,
      G.eventually_subset_sourceCoordinateChart q (isCompact_closedBall a r) hsmall] with k hkb hk i j
    obtain ⟨he, hei⟩ := G.sourceCoordinateChart_smooth k q
    have hdom : Metric.ball a (r / 2) ×ˢ Icc α β ⊆
        RicciFlow.BackwardCoordinates.domain (Iio 0) (G.sourceCoordinateChart k q) := by
      intro z hz
      exact ⟨hk (hUC hz.1), by simpa only [interior_Iio, mem_preimage, mem_Iio] using neg_neg_of_pos (hα.trans_le hz.2.1)⟩
    have hc := (RicciFlow.BackwardCoordinates.contDiffOn_weightedPrincipal
      (S.rescaling (G.subsequence k)).flow (G.sourceCoordinateChart k q)
      he hei i j).continuousOn.mono hdom
    apply memLp_top_of_bound (C := C)
    · dsimp only [μ]
      rw [Measure.prod_restrict]
      exact (hc.comp continuous_swap.continuousOn (fun z hz => ⟨hz.2, hz.1⟩)).aestronglyMeasurable
        (measurableSet_Icc.prod measurableSet_ball)
    · filter_upwards [hmem] with z hz
      exact hkb z.swap ⟨hUC hz.2, hz.1⟩ i j
  have hB (i j : Fin n) : MemLp
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) => LeviCivitaData.Dirichlet.divergenceCoefficients
        (G.limit.flow.metric (-z.1)) e z.2 i j) ∞ μ := by
    have hdom : Metric.ball a (r / 2) ×ˢ Icc α β ⊆
        RicciFlow.BackwardCoordinates.domain (Iio 0) e := by
      intro z hz
      exact ⟨hsmall (hUC hz.1), by simpa only [interior_Iio, mem_preimage, mem_Iio] using neg_neg_of_pos (hα.trans_le hz.2.1)⟩
    have hc := (RicciFlow.BackwardCoordinates.contDiffOn_weightedPrincipal G.limit.flow e
      contMDiffOn_chart_symm contMDiffOn_chart i j).continuousOn.mono hdom
    apply memLp_top_of_bound (C := C)
    · dsimp only [μ]
      rw [Measure.prod_restrict]
      exact (hc.comp continuous_swap.continuousOn (fun z hz => ⟨hz.2, hz.1⟩)).aestronglyMeasurable
        (measurableSet_Icc.prod measurableSet_ball)
    · filter_upwards [hmem] with z hz
      have hz' : z.swap ∈ Metric.closedBall a r ×ˢ Icc α β := ⟨hUC hz.2, hz.1⟩
      have hc := hconv.tendsto_at (x := z.swap) hz'
      have hp := ((continuous_apply j).tendsto _).comp
        (((continuous_apply i).tendsto _).comp hc)
      apply le_of_tendsto hp.norm
      filter_upwards [hcoeff] with k hk
      exact hk z.swap ⟨hUC hz.2, hz.1⟩ i j
  constructor
  · change MemLp (fun z => G.limitReducedLengthGradientEnergy q l z) ∞ μ
    simpa only [limitReducedLengthGradientEnergy, v, e,
      LeviCivitaData.Dirichlet.sum_divergenceCoefficients_eq_inverse_pairing] using
      Poincare.Analysis.Elliptic.memLp_top_spatial_gradient_quadratic_of_lipschitz
        Metric.isOpen_ball measurableSet_ball hUO measurableSet_Icc hv hB
  · filter_upwards [hu, hA] with k hku hkA
    change MemLp (fun z => G.reducedLengthPullbackGradientEnergy k q z) ∞ μ
    simpa only [reducedLengthPullbackGradientEnergy, u, e,
      LeviCivitaData.Dirichlet.sum_divergenceCoefficients_eq_inverse_pairing] using
      Poincare.Analysis.Elliptic.memLp_top_spatial_gradient_quadratic_of_lipschitz
        Metric.isOpen_ball measurableSet_ball hUO measurableSet_Icc hku hkA

theorem tendsto_integral_reducedLength_gradient_energy_sub_abs
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop
        (univ ×ˢ Ioi (0 : ℝ)))
    (q : G.limit.carrier.carrier) {a : EuclideanSpace ℝ (Fin n)} {r α β : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hαβ : α ≤ β)
    (hchart : Metric.closedBall a (2 * r) ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target) :
    let μ := (volume.restrict (Icc α β)).prod (volume.restrict (Metric.ball a (r / 2)))
    Tendsto (fun k => ∫ z, |G.reducedLengthPullbackGradientEnergy (σ k) q z -
      G.limitReducedLengthGradientEnergy q l z| ∂μ) atTop (𝓝 0) := by
  have hm := G.reducedLength_gradient_energies_memLp_top P hσ l hlim q hr hα hαβ hchart
  let : IsFiniteMeasure (volume.restrict (Metric.ball a (r / 2))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  apply (G.tendsto_iterated_integral_reducedLengthPullback_gradient_energy_sub_abs
    P hσ l hlim q hr hα hαβ hchart).congr'
  filter_upwards [hσ.tendsto_atTop.eventually hm.2] with k hk
  exact (integral_prod _ ((hk.integrable le_top).sub (hm.1.integrable le_top)).norm).symm

theorem exists_subseq_reducedLength_gradient_energy_tendsto_ae
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop
        (univ ×ˢ Ioi (0 : ℝ)))
    (q : G.limit.carrier.carrier) {a : EuclideanSpace ℝ (Fin n)} {r α β : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hαβ : α ≤ β)
    (hchart : Metric.closedBall a (2 * r) ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target) :
    ∃ η : ℕ → ℕ, StrictMono η ∧
      ∀ᵐ z ∂(volume.restrict (Icc α β)).prod (volume.restrict (Metric.ball a (r / 2))),
        Tendsto (fun k => G.reducedLengthPullbackGradientEnergy (σ (η k)) q z) atTop
          (𝓝 (G.limitReducedLengthGradientEnergy q l z)) := by
  have hm := G.reducedLength_gradient_energies_memLp_top P hσ l hlim q hr hα hαβ hchart
  let : IsFiniteMeasure (volume.restrict (Metric.ball a (r / 2))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  exact Poincare.Analysis.exists_subseq_tendsto_ae_of_integral_abs_sub
    ((hσ.tendsto_atTop.eventually hm.2).mono fun _ hk => hk.integrable le_top)
    (hm.1.integrable le_top)
    (G.tendsto_integral_reducedLength_gradient_energy_sub_abs P hσ l hlim q hr hα hαβ hchart)

end PoincareConjecture.AncientCompactTimeConvergence
