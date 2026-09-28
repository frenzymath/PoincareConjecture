import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.AncientFlux
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.AncientReaction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.FluxIntegrability
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.RescaledEquations
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.IntegralTests

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
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}

theorem limitReducedLength_second_weak_coordinate_gradient_inequality
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop
        (univ ×ˢ Ioi (0 : ℝ)))
    (q : G.limit.carrier.carrier) {a : EuclideanSpace ℝ (Fin n)} {r τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ)
    (hchart : Metric.closedBall a (2 * r) ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφO : tsupport φ ⊆ Metric.ball a (r / 2))
    (hφ0 : ∀ x, 0 ≤ φ x) :
    let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
    let g := G.limit.flow.metric (-τ)
    let v := fun x => l (e x, τ)
    let B := fun x => (φ x *
      (-fderiv ℝ v x ((g.pullbackCoefficients e x).inverse (fderiv ℝ v x)) +
        (G.limit.flow.connection (-τ)).scalarCurvature (e x) + (v x - (n : ℝ)) / τ) -
      2 * fderiv ℝ φ x ((g.pullbackCoefficients e x).inverse (fderiv ℝ v x))) *
      g.pullbackVolumeDensity e x
    IntegrableOn B (Metric.ball a (r / 2)) ∧
      (∫ x in Metric.ball a (r / 2), B x) ≤ 0 := by
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  let g := G.limit.flow.metric (-τ)
  let ek := fun k => G.sourceCoordinateChart (σ k) q
  let gk := fun k => (S.rescaling (G.subsequence (σ k))).flow.metric (-τ)
  let O := Metric.ball a (r / 2)
  let u := fun k x => G.reducedLengthPullback (σ k) (e x) τ
  let v := fun x => l (e x, τ)
  let E := fun k x => (gk k).pullbackVolumeDensity (ek k) x *
    fderiv ℝ (u k) x (((gk k).pullbackCoefficients (ek k) x).inverse (fderiv ℝ (u k) x))
  let E₀ := fun x => g.pullbackVolumeDensity e x *
    fderiv ℝ v x ((g.pullbackCoefficients e x).inverse (fderiv ℝ v x))
  let J := fun k x => (gk k).pullbackVolumeDensity (ek k) x *
    fderiv ℝ φ x (((gk k).pullbackCoefficients (ek k) x).inverse (fderiv ℝ (u k) x))
  let J₀ := fun x => g.pullbackVolumeDensity e x *
    fderiv ℝ φ x ((g.pullbackCoefficients e x).inverse (fderiv ℝ v x))
  let H := fun k x => φ x *
    (((S.rescaling (G.subsequence (σ k))).flow.connection (-τ)).scalarCurvature (ek k x) +
      (u k x - (n : ℝ)) / τ) * (gk k).pullbackVolumeDensity (ek k) x
  let H₀ := fun x => φ x * ((G.limit.flow.connection (-τ)).scalarCurvature (e x) +
    (v x - (n : ℝ)) / τ) * g.pullbackVolumeDensity e x
  let B := fun k x => H k x - φ x * E k x - 2 * J k x
  let B₀ := fun x => H₀ x - φ x * E₀ x - 2 * J₀ x
  have hsmall : Metric.closedBall a r ⊆ e.source :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hchart
  have hUO : O ⊆ Metric.ball a r := Metric.ball_subset_ball (by linarith)
  have hUC : O ⊆ Metric.closedBall a r := hUO.trans Metric.ball_subset_closedBall
  have hclosure : closure O = Metric.closedBall a (r / 2) := closure_ball a (half_pos hr).ne'
  have hOc : IsCompact (closure O) := hclosure ▸ isCompact_closedBall _ _
  have hclose : closure O ⊆ Metric.closedBall a r := by
    rw [hclosure]
    exact Metric.closedBall_subset_closedBall (by linarith)
  obtain ⟨L, C, hC, hdata⟩ := G.exists_eventually_reducedLengthPullback_weak_data_bounds
    P q hr hτ hchart
  have hu : ∀ᶠ k in atTop, LipschitzOnWith L (u k) (Metric.ball a r) :=
    (hσ.tendsto_atTop.eventually hdata).mono fun _ hk => hk.1
  have hv : LipschitzOnWith L v (Metric.ball a r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    apply le_of_tendsto ((hlim.tendsto_at (show (e x, τ) ∈ univ ×ˢ Ioi (0 : ℝ)
      from ⟨mem_univ _, hτ⟩)).dist
      (hlim.tendsto_at (show (e y, τ) ∈ univ ×ˢ Ioi (0 : ℝ) from ⟨mem_univ _, hτ⟩)))
    exact hu.mono fun k hk => hk.dist_le_mul x hx y hy
  have hE₀ : IntegrableOn E₀ O := g.integrableOn_coordinate_gradient_energy e
    contMDiffOn_chart_symm contMDiffOn_chart Metric.isOpen_ball hOc
    (hclose.trans hsmall) (hv.mono hUO)
  have hJ₀ : IntegrableOn J₀ O := g.integrableOn_coordinate_gradient_pairing e
    contMDiffOn_chart_symm contMDiffOn_chart Metric.isOpen_ball hOc
    (hclose.trans hsmall) (hv.mono hUO) hφ
  have hEJ : ∀ᶠ k in atTop, IntegrableOn (E k) O ∧ IntegrableOn (J k) O := by
    filter_upwards [hσ.tendsto_atTop.eventually hdata] with k hk
    obtain ⟨he, hei⟩ := G.sourceCoordinateChart_smooth (σ k) q
    exact ⟨(gk k).integrableOn_coordinate_gradient_energy (ek k) he hei
      Metric.isOpen_ball hOc (hclose.trans hk.2.1) (hk.1.mono hUO),
      (gk k).integrableOn_coordinate_gradient_pairing (ek k) he hei
        Metric.isOpen_ball hOc (hclose.trans hk.2.1) (hk.1.mono hUO) hφ⟩
  obtain ⟨D, hD⟩ := hφc.exists_bound_of_continuous hφ.continuous
  have hφm : AEStronglyMeasurable φ (volume.restrict O) := hφ.continuous.aestronglyMeasurable
  have hφb : ∀ᵐ x ∂volume.restrict O, |φ x| ≤ D := Eventually.of_forall hD
  have hφE₀ : IntegrableOn (fun x => φ x * E₀ x) O := hE₀.bdd_mul hφm hφb
  have hφE : ∀ᶠ k in atTop, IntegrableOn (fun x => φ x * E k x) O :=
    hEJ.mono fun k hk => hk.1.bdd_mul hφm hφb
  have hElim : Tendsto (fun k => ∫ x in O, φ x * E k x) atTop
      (𝓝 (∫ x in O, φ x * E₀ x)) :=
    Poincare.Analysis.Elliptic.tendsto_integral_test_mul_of_integral_abs_sub
      (hEJ.mono fun _ hk => hk.1) hE₀ hφm hφb
      (G.tendsto_integral_reducedLengthPullback_gradient_energy_sub_abs P hσ l hlim q hr hτ hchart)
  have hJlim : Tendsto (fun k => ∫ x in O, J k x) atTop (𝓝 (∫ x in O, J₀ x)) :=
    Poincare.Analysis.Elliptic.tendsto_integral_of_integral_abs_sub
      (hEJ.mono fun _ hk => hk.2) hJ₀
      (G.tendsto_integral_reducedLengthPullback_test_flux_sub_abs P hσ l hlim q hr hτ hchart hφ)
  obtain ⟨hH₀, hH, hHlim⟩ := G.reducedLengthPullback_reaction_integrable_tendsto
    P hσ l hlim q hr hτ hchart hφ.continuous
  change IntegrableOn H₀ O at hH₀
  change ∀ᶠ k in atTop, IntegrableOn (H k) O at hH
  change Tendsto (fun k => ∫ x in O, H k x) atTop (𝓝 (∫ x in O, H₀ x)) at hHlim
  have hB₀ : IntegrableOn B₀ O := (hH₀.sub hφE₀).sub (hJ₀.const_mul 2)
  have hBlim : Tendsto (fun k => ∫ x in O, B k x) atTop (𝓝 (∫ x in O, B₀ x)) := by
    have h := (hHlim.sub hElim).sub (hJlim.const_mul 2)
    have hlim_eq : ((∫ x in O, H₀ x) - ∫ x in O, φ x * E₀ x) -
        2 * ∫ x in O, J₀ x = ∫ x in O, B₀ x := by
      have hs := integral_sub (hH₀.sub hφE₀) (hJ₀.const_mul 2)
      simp only [Pi.sub_apply, integral_const_mul] at hs
      rw [integral_sub hH₀ hφE₀] at hs
      exact hs.symm
    rw [hlim_eq] at h
    apply h.congr'
    filter_upwards [hH, hφE, hEJ] with k hkH hkE hkJ
    have hs := integral_sub (hkH.sub hkE) (hkJ.2.const_mul 2)
    simp only [Pi.sub_apply, integral_const_mul] at hs
    rw [integral_sub hkH hkE] at hs
    exact hs.symm
  have hBnonpos : ∀ᶠ k in atTop, (∫ x in O, B k x) ≤ 0 := by
    filter_upwards [hσ.tendsto_atTop.eventually hdata,
      hσ.tendsto_atTop.eventually (eventually_timeWindow_mem_nhds (by norm_num : (-1 : ℝ) < 0))]
      with k hk hk₀
    obtain ⟨he, hei⟩ := G.sourceCoordinateChart_smooth (σ k) q
    have h := (S.rescaling (G.subsequence (σ k))).reducedLength_second_weak_coordinate_gradient_inequality
      P S.reference hτ (ek k) he hei Metric.isOpen_ball (hUC.trans hk.2.1) hφ hφc hφO hφ0
    have hfun := G.reducedLengthPullback_coordinates_eq (σ k) q hk₀ τ
    change (fun x => reducedLength K.flow 0 S.reference (ek k x)
      (S.scale (G.subsequence (σ k)) * τ)) = u k at hfun
    dsimp only at h
    simp only [hfun, congrFun hfun] at h
    convert h.2 using 1
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    dsimp only [B, H, E, J, u, gk, ek]
    ring
  have hle : (∫ x in O, B₀ x) ≤ 0 := le_of_tendsto hBlim hBnonpos
  have heq : B₀ = fun x => (φ x *
      (-fderiv ℝ v x ((g.pullbackCoefficients e x).inverse (fderiv ℝ v x)) +
        (G.limit.flow.connection (-τ)).scalarCurvature (e x) + (v x - (n : ℝ)) / τ) -
      2 * fderiv ℝ φ x ((g.pullbackCoefficients e x).inverse (fderiv ℝ v x))) *
      g.pullbackVolumeDensity e x := by
    funext x
    dsimp only [B₀, H₀, E₀, J₀]
    ring
  rw [heq] at hB₀ hle
  exact ⟨hB₀, hle⟩

end PoincareConjecture.AncientCompactTimeConvergence
