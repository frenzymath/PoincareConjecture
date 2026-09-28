import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.AncientEnergy
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.TimeCoordinates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.RescaledEquations

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

private theorem ae_timeEquation_of_slices
    {I : Set ℝ} {O : Set (EuclideanSpace ℝ (Fin n))}
    {u ρ Q R : ℝ × EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hI : IsOpen I) (hO : IsOpen O) (hu : LipschitzOnWith L u (I ×ˢ O))
    (hρ : AEStronglyMeasurable ρ ((volume.restrict I).prod (volume.restrict O)))
    (hQ : AEStronglyMeasurable Q ((volume.restrict I).prod (volume.restrict O)))
    (hR : AEStronglyMeasurable R ((volume.restrict I).prod (volume.restrict O)))
    (hslice : ∀ τ ∈ I, ∀ᵐ x ∂volume.restrict O,
      2 * deriv (fun s => u (s, x)) τ + Q (τ, x) / ρ (τ, x) - R (τ, x) +
        u (τ, x) / τ = 0) :
    ∀ᵐ z ∂(volume.restrict I).prod (volume.restrict O),
      2 * fderiv ℝ u z (1, 0) + Q z / ρ z - R z + u z / z.1 = 0 := by
  have hum : AEStronglyMeasurable u ((volume.restrict I).prod (volume.restrict O)) := by
    rw [Measure.prod_restrict]
    exact hu.continuousOn.aestronglyMeasurable (hI.measurableSet.prod hO.measurableSet)
  have hdm : AEStronglyMeasurable (fun z => fderiv ℝ u z (1, 0))
      ((volume.restrict I).prod (volume.restrict O)) := by
    rw [Measure.prod_restrict]
    exact (Poincare.Analysis.Elliptic.memLp_top_directional_fderiv_of_lipschitzOn
      (μ := volume) (hI.prod hO) hu (1, 0)).aestronglyMeasurable
  have hm : AEStronglyMeasurable (fun z => 2 * fderiv ℝ u z (1, 0) +
      Q z / ρ z - R z + u z / z.1) ((volume.restrict I).prod (volume.restrict O)) :=
    (((hdm.const_mul 2).add
      (hQ.aemeasurable.div hρ.aemeasurable).aestronglyMeasurable).sub hR).add
      (hum.aemeasurable.div continuous_fst.aemeasurable).aestronglyMeasurable
  apply Poincare.Analysis.Elliptic.ae_eq_zero_of_ae_slices hm
  have hd := Measure.ae_ae_of_ae_prod
    (Poincare.Analysis.Elliptic.ae_time_slice_deriv_eq_fderiv_of_lipschitz hI hO hu)
  filter_upwards [ae_restrict_mem hI.measurableSet, hd] with τ hτ hdτ
  filter_upwards [hslice τ hτ, hdτ] with x hx hdx
  rwa [hdx] at hx

private theorem ae_sourceCoordinateChart_timeEquation
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    (k : ℕ) (q : G.limit.carrier.carrier)
    (hk : ancientM18TimeWindow k ∈ 𝓝 (-1 : ℝ)) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᵐ x, x ∈ (G.sourceCoordinateChart k q).source →
      let e := G.sourceCoordinateChart k q
      let F := (S.rescaling (G.subsequence k)).flow
      let u := fun s => G.reducedLengthPullback k
        ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm x) s
      2 * deriv u τ + G.reducedLengthPullbackGradientEnergy k q (τ, x) /
        (F.metric (-τ)).pullbackVolumeDensity e x -
        (F.connection (-τ)).scalarCurvature (e x) + u τ / τ = 0 := by
  let e := G.sourceCoordinateChart k q
  let F := (S.rescaling (G.subsequence k)).flow
  obtain ⟨he, hei⟩ := G.sourceCoordinateChart_smooth k q
  have hHJ := (S.rescaling (G.subsequence k)).ae_reducedLength_hamiltonJacobi_coordinates
    P S.reference hτ e he hei
  filter_upwards [hHJ] with x hx hxsource
  have hh := hx hxsource
  have hspace :
      (fun y : EuclideanSpace ℝ (Fin n) => reducedLength K.flow 0 S.reference (e y)
        (S.scale (G.subsequence k) * τ)) =
      (fun y => G.reducedLengthPullback k
        ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm y) τ) :=
    G.reducedLengthPullback_coordinates_eq k q hk τ
  have htime : (fun b => reducedLength K.flow 0 S.reference (e x)
      (S.scale (G.subsequence k) * b)) = fun b => G.reducedLengthPullback k
        ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm x) b := by
    funext b
    exact congrFun (G.reducedLengthPullback_coordinates_eq k q hk b) x
  dsimp only at hh ⊢
  simp only [hspace, congrFun hspace, htime] at hh
  have hρpos : 0 < (F.metric (-τ)).pullbackVolumeDensity e x :=
    RicciFlow.BackwardCoordinates.density_pos F e he hei (z := (x, τ)) hxsource
  change 2 * deriv _ τ +
    ((F.metric (-τ)).pullbackVolumeDensity e x * _) /
      (F.metric (-τ)).pullbackVolumeDensity e x - _ + _ = 0
  rw [mul_div_cancel_left₀ _ hρpos.ne']
  exact hh

private theorem aestronglyMeasurable_swap_of_continuousOn
    {O : Set (EuclideanSpace ℝ (Fin n))} {I : Set ℝ}
    {f : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    (hI : IsOpen I) (hO : IsOpen O) (hf : ContinuousOn f (O ×ˢ I)) :
    AEStronglyMeasurable (fun z : ℝ × EuclideanSpace ℝ (Fin n) => f (z.2, z.1))
      ((volume.restrict I).prod (volume.restrict O)) := by
  rw [Measure.prod_restrict]
  have hc : ContinuousOn (fun z : ℝ × EuclideanSpace ℝ (Fin n) => f (z.2, z.1))
      (I ×ˢ O) :=
    hf.comp (continuous_swap.continuousOn : ContinuousOn
      (Prod.swap : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) × ℝ) (I ×ˢ O))
      (show MapsTo Prod.swap (I ×ˢ O) (O ×ˢ I) from fun _ hz => ⟨hz.2, hz.1⟩)
  exact hc.aestronglyMeasurable (hI.measurableSet.prod hO.measurableSet)

private theorem positive_time_domain_subset
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hOs : O ⊆ e.source)
    {α β : ℝ} (hα : 0 < α) :
    O ×ˢ Ioo α β ⊆ RicciFlow.BackwardCoordinates.domain (Iio 0) e := by
  intro z hz
  exact ⟨hOs hz.1, by
    simpa only [interior_Iio, mem_preimage, mem_Iio] using neg_neg_of_pos (hα.trans hz.2.1)⟩

private theorem time_density_measurable
    (F : RicciFlow n M (Iio 0))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (hOs : O ⊆ e.source)
    {α β : ℝ} (hα : 0 < α) :
    AEStronglyMeasurable (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
      (F.metric (-z.1)).pullbackVolumeDensity e z.2)
      ((volume.restrict (Ioo α β)).prod (volume.restrict O)) := by
  have hc : ContinuousOn (RicciFlow.BackwardCoordinates.density F e) (O ×ˢ Ioo α β) :=
    (RicciFlow.BackwardCoordinates.contDiffOn_density F e he hei).continuousOn.mono
      (positive_time_domain_subset e hOs hα)
  exact aestronglyMeasurable_swap_of_continuousOn
    (f := RicciFlow.BackwardCoordinates.density F e) isOpen_Ioo hO hc

private theorem time_scalar_measurable
    (F : RicciFlow n M (Iio 0))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (hOs : O ⊆ e.source)
    {α β : ℝ} (hα : 0 < α) :
    AEStronglyMeasurable (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
      (F.connection (-z.1)).scalarCurvature (e z.2))
      ((volume.restrict (Ioo α β)).prod (volume.restrict O)) := by
  have hc : ContinuousOn (fun z : EuclideanSpace ℝ (Fin n) × ℝ =>
      (F.connection (-z.2)).scalarCurvature (e z.1)) (O ×ˢ Ioo α β) :=
    (RicciFlow.BackwardCoordinates.contDiffOn_scalarCurvature_coordinates F e he hei).continuousOn.mono
      (positive_time_domain_subset e hOs hα)
  exact aestronglyMeasurable_swap_of_continuousOn
    (f := fun z : EuclideanSpace ℝ (Fin n) × ℝ =>
      (F.connection (-z.2)).scalarCurvature (e z.1)) isOpen_Ioo hO hc

theorem eventually_ae_reducedLengthPullback_time_equation
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop
        (univ ×ˢ Ioi (0 : ℝ)))
    (q : G.limit.carrier.carrier) {a : EuclideanSpace ℝ (Fin n)} {r α β : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hαβ : α ≤ β)
    (hchart : Metric.closedBall a (2 * r) ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target) :
    ∀ᶠ k in atTop,
      ∀ᵐ z ∂(volume.restrict (Ioo α β)).prod (volume.restrict (Metric.ball a (r / 2))),
        let e := G.sourceCoordinateChart k q
        let g := (S.rescaling (G.subsequence k)).flow.metric (-z.1)
        let u := fun w : ℝ × EuclideanSpace ℝ (Fin n) =>
          G.reducedLengthPullback k ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm w.2) w.1
        2 * fderiv ℝ u z (1, 0) +
          G.reducedLengthPullbackGradientEnergy k q z / g.pullbackVolumeDensity e z.2 -
          ((S.rescaling (G.subsequence k)).flow.connection (-z.1)).scalarCurvature (e z.2) +
          u z / z.1 = 0 := by
  let c := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  let O := Metric.ball a (r / 2)
  let I := Ioo α β
  let μ := (volume.restrict I).prod (volume.restrict O)
  have hUC : O ⊆ Metric.closedBall a r :=
    (Metric.ball_subset_ball (by linarith : r / 2 ≤ r)).trans Metric.ball_subset_closedBall
  have hsmall : Metric.closedBall a r ⊆ c.source :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hchart
  obtain ⟨L, C, hC, hLip⟩ := G.reducedLengthPullback_eventually_lipschitz_on_chart_cylinder
    P q hr hα hαβ hchart
  have henergy := (G.reducedLength_gradient_energies_memLp_top
    P hσ l hlim q hr hα hαβ hchart).2
  filter_upwards [hLip, henergy,
    G.eventually_subset_sourceCoordinateChart q (isCompact_closedBall a r) hsmall,
    eventually_timeWindow_mem_nhds (by norm_num : (-1 : ℝ) < 0)] with k hk hkE hkchart hk₀
  let e := G.sourceCoordinateChart k q
  let F := (S.rescaling (G.subsequence k)).flow
  let u := fun z : ℝ × EuclideanSpace ℝ (Fin n) => G.reducedLengthPullback k (c z.2) z.1
  let ρ := fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
    (F.metric (-z.1)).pullbackVolumeDensity e z.2
  let R := fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
    (F.connection (-z.1)).scalarCurvature (e z.2)
  have hu : LipschitzOnWith L u (I ×ˢ O) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    simpa only [u, c, Prod.swap, Prod.dist_eq, max_comm] using hk.1.dist_le_mul z.swap
      ⟨hUC hz.2, ⟨hz.1.1.le, hz.1.2.le⟩⟩ w.swap
      ⟨hUC hw.2, ⟨hw.1.1.le, hw.1.2.le⟩⟩
  obtain ⟨he, hei⟩ := G.sourceCoordinateChart_smooth k q
  have hρm : AEStronglyMeasurable ρ μ := time_density_measurable F e he hei
    Metric.isOpen_ball (hUC.trans hkchart) hα
  have hRm : AEStronglyMeasurable R μ := time_scalar_measurable F e he hei
    Metric.isOpen_ball (hUC.trans hkchart) hα
  have hEm : AEStronglyMeasurable (G.reducedLengthPullbackGradientEnergy k q) μ := by
    simpa only [μ, I, O, restrict_Ioo_eq_restrict_Icc] using hkE.aestronglyMeasurable
  apply ae_timeEquation_of_slices isOpen_Ioo Metric.isOpen_ball hu hρm hEm hRm
  intro τ hτ
  have hτpos : 0 < τ := hα.trans hτ.1
  have hHJ := G.ae_sourceCoordinateChart_timeEquation P k q hk₀ hτpos
  filter_upwards [ae_restrict_of_ae hHJ, ae_restrict_mem measurableSet_ball] with x hx hxO
  exact hx (hkchart (hUC hxO))

end PoincareConjecture.AncientCompactTimeConvergence
