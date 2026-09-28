import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.AncientScalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.AncientQuadratic


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

theorem reducedLengthPullback_reaction_integrable_tendsto
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop
        (univ ×ˢ Ioi (0 : ℝ)))
    (q : G.limit.carrier.carrier) {a : EuclideanSpace ℝ (Fin n)} {r τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ)
    (hchart : Metric.closedBall a (2 * r) ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : Continuous φ) :
    let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
    let H := fun k x => φ x *
      (((S.rescaling (G.subsequence (σ k))).flow.connection (-τ)).scalarCurvature
          (G.sourceCoordinateChart (σ k) q x) +
        (G.reducedLengthPullback (σ k) (e x) τ - (n : ℝ)) / τ) *
      ((S.rescaling (G.subsequence (σ k))).flow.metric (-τ)).pullbackVolumeDensity
        (G.sourceCoordinateChart (σ k) q) x
    let H₀ := fun x => φ x * ((G.limit.flow.connection (-τ)).scalarCurvature (e x) +
      (l (e x, τ) - (n : ℝ)) / τ) * (G.limit.flow.metric (-τ)).pullbackVolumeDensity e x
    IntegrableOn H₀ (Metric.ball a (r / 2)) ∧
      (∀ᶠ k in atTop, IntegrableOn (H k) (Metric.ball a (r / 2))) ∧
      Tendsto (fun k => ∫ x in Metric.ball a (r / 2), H k x) atTop
        (𝓝 (∫ x in Metric.ball a (r / 2), H₀ x)) := by
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  let O := Metric.ball a (r / 2)
  let A := Metric.closedBall a r
  let u := fun k x => G.reducedLengthPullback (σ k) (e x) τ
  let v := fun x => l (e x, τ)
  let ρ := fun k x => ((S.rescaling (G.subsequence (σ k))).flow.metric (-τ)).pullbackVolumeDensity
    (G.sourceCoordinateChart (σ k) q) x
  let R := fun k x => ((S.rescaling (G.subsequence (σ k))).flow.connection (-τ)).scalarCurvature
    (G.sourceCoordinateChart (σ k) q x)
  let ρ₀ := (G.limit.flow.metric (-τ)).pullbackVolumeDensity e
  let R₀ := fun x => (G.limit.flow.connection (-τ)).scalarCurvature (e x)
  let H := fun k x => φ x * (R k x + (u k x - (n : ℝ)) / τ) * ρ k x
  let H₀ := fun x => φ x * (R₀ x + (v x - (n : ℝ)) / τ) * ρ₀ x
  have hOA : O ⊆ A :=
    (Metric.ball_subset_ball (by linarith : r / 2 ≤ r)).trans Metric.ball_subset_closedBall
  have hsmall : A ⊆ e.source := (Metric.closedBall_subset_closedBall (by linarith)).trans hchart
  let : IsFiniteMeasure (volume.restrict O) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  obtain ⟨L, C, hC, hLip⟩ := G.reducedLengthPullback_eventually_lipschitz_on_chart_cylinder
    P q hr hτ (le_refl τ) hchart
  have hu : ∀ᶠ k in atTop, LipschitzOnWith L (u k) A ∧ ∀ x ∈ A, 0 ≤ u k x ∧ u k x ≤ C := by
    filter_upwards [hσ.tendsto_atTop.eventually hLip] with k hk
    refine ⟨?_, fun x hx => hk.2 (x, τ) ⟨hx, ⟨le_rfl, le_rfl⟩⟩⟩
    simpa only [mul_one, Function.comp_def] using hk.1.comp
      (LipschitzWith.prodMk_right τ).lipschitzOnWith (fun x hx => ⟨hx, ⟨le_rfl, le_rfl⟩⟩)
  have hpoint (x) : Tendsto (fun k => u k x) atTop (𝓝 (v x)) :=
    hlim.tendsto_at (show (e x, τ) ∈ univ ×ˢ Ioi (0 : ℝ) from ⟨mem_univ _, hτ⟩)
  have hv : LipschitzOnWith L v A := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    apply le_of_tendsto ((hpoint x).dist (hpoint y))
    exact hu.mono fun k hk => hk.1.dist_le_mul x hx y hy
  have hρ₀ : ContinuousOn ρ₀ A := by
    have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
      ⟨(contMDiffOn_chart_symm (n := ∞)).mdifferentiableOn (by simp),
        (contMDiffOn_chart (n := ∞)).mdifferentiableOn (by simp)⟩
    intro x hx
    exact ((G.limit.flow.metric (-τ)).contDiffAt_pullbackVolumeDensity
      (contMDiffOn_chart_symm.contMDiffAt (e.open_source.mem_nhds (hsmall hx)))
      (hD.mfderiv_injective (hsmall hx))).1.continuousAt.continuousWithinAt
  have hR₀ : ContinuousOn R₀ A :=
    (G.limit.flow.connection (-τ)).continuous_scalarCurvature.comp_continuousOn
      (e.continuousOn.mono hsmall)
  have hH₀ : ContinuousOn H₀ A :=
    (hφ.continuousOn.mul (hR₀.add ((hv.continuousOn.sub continuousOn_const).div_const τ))).mul hρ₀
  have hH₀i : IntegrableOn H₀ O :=
    hH₀.integrableOn_of_subset_isCompact (isCompact_closedBall a r) measurableSet_ball hOA
      (measure_ball_lt_top.ne)
  have hρlim := G.tendstoUniformlyOn_sourceCoordinateChart_volumeDensity q
    (isCompact_closedBall a r) hsmall hτ
  have hHl : ∀ᵐ x ∂volume.restrict O, Tendsto (fun k => H k x) atTop (𝓝 (H₀ x)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (((G.tendsto_sourceCoordinateChart_scalarCurvature q x hτ).comp hσ.tendsto_atTop).add
      (((hpoint x).sub_const (n : ℝ)).div_const τ)).const_mul (φ x) |>.mul
        ((hρlim.tendsto_at (hOA hx)).comp hσ.tendsto_atTop)
  have hHm : ∀ᶠ k in atTop, AEStronglyMeasurable (H k) (volume.restrict O) := by
    filter_upwards [hu, hσ.tendsto_atTop.eventually
      (G.eventually_subset_sourceCoordinateChart q (isCompact_closedBall a r) hsmall)] with k hk hkchart
    let ek := G.sourceCoordinateChart (σ k) q
    obtain ⟨he, hei⟩ := G.sourceCoordinateChart_smooth (σ k) q
    have hD : ek.MDifferentiable (𝓡 n) (𝓡 n) :=
      ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
    have hρc : ContinuousOn (ρ k) O := by
      intro x hx
      exact (((S.rescaling (G.subsequence (σ k))).flow.metric (-τ)).contDiffAt_pullbackVolumeDensity
        (he.contMDiffAt (ek.open_source.mem_nhds (hkchart (hOA hx))))
        (hD.mfderiv_injective (hkchart (hOA hx)))).1.continuousAt.continuousWithinAt
    have hRc : ContinuousOn (R k) O :=
      ((S.rescaling (G.subsequence (σ k))).flow.connection (-τ)).continuous_scalarCurvature.comp_continuousOn
        (ek.continuousOn.mono (hOA.trans hkchart))
    exact ((hφ.continuousOn.mul (hRc.add (((hk.1.continuousOn.mono hOA).sub
      continuousOn_const).div_const τ))).mul hρc).aestronglyMeasurable measurableSet_ball
  obtain ⟨D₀, hD₀⟩ := (isCompact_closedBall a r).exists_bound_of_continuousOn hφ.continuousOn
  let D := max D₀ 0
  have hD : 0 ≤ D := le_max_right _ _
  obtain ⟨Cρ, hCρ, hρb⟩ := G.exists_eventually_sourceCoordinateChart_coefficient_bounds
    q (isCompact_closedBall a r) hsmall hτ
  obtain ⟨CR, hCR, hRb⟩ := G.exists_eventually_sourceCoordinateChart_scalar_bound P q hr hτ hchart
  have hHb : ∀ᶠ k in atTop, ∀ᵐ x ∂volume.restrict O,
      ‖H k x‖ ≤ D * (CR + (C + (n : ℝ)) / τ) * Cρ := by
    filter_upwards [hu, hσ.tendsto_atTop.eventually hρb, hσ.tendsto_atTop.eventually hRb]
      with k hk hkρ hkR
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hxA := hOA hx
    have hub := hk.2 x hxA
    have hRabs : |R k x| ≤ CR := by rw [abs_of_nonneg (hkR x hxA).1]; exact (hkR x hxA).2
    have huabs : |u k x - (n : ℝ)| ≤ C + (n : ℝ) :=
      (abs_sub _ _).trans (by rw [abs_of_nonneg hub.1, abs_of_nonneg (Nat.cast_nonneg n)]; linarith)
    have hsum : |R k x + (u k x - (n : ℝ)) / τ| ≤ CR + (C + (n : ℝ)) / τ := by
      apply (abs_add_le _ _).trans
      exact add_le_add hRabs (by rw [abs_div, abs_of_pos hτ]; exact div_le_div_of_nonneg_right huabs hτ.le)
    dsimp only [H]
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul ((hD₀ x hxA).trans (le_max_left _ _)) hsum
      (abs_nonneg _) hD) (hkρ x hxA).1 (abs_nonneg _) (mul_nonneg hD (by positivity))
  refine ⟨hH₀i, ?_, ?_⟩
  · filter_upwards [hHm, hHb] with k hkm hkb
    exact (memLp_top_of_bound hkm _ hkb).integrable le_top
  · exact tendsto_integral_filter_of_norm_le_const hHm ⟨_, hHb⟩ hHl

end PoincareConjecture.AncientCompactTimeConvergence
