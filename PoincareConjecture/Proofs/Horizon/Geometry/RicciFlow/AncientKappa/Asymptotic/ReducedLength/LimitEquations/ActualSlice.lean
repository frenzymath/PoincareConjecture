import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.LimitEquations.Exponential.HeatSlice
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.AncientHamiltonJacobi
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.AncientSecondInequality
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Extraction.Ancient.LimitRegularity

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal

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

theorem ae_limitReducedLength_heat_weak_coordinate_gradient
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop
        (univ ×ˢ Ioi (0 : ℝ)))
    (q : G.limit.carrier.carrier) {a : EuclideanSpace ℝ (Fin n)} {r α β : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hαβ : α ≤ β)
    (hchart : Metric.closedBall a (2 * r) ⊆
      (chartAt (EuclideanSpace ℝ (Fin n)) q).target) :
    ∀ᵐ τ ∂volume.restrict (Ioo α β),
      ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ Metric.ball a (r / 2) → (∀ x, 0 ≤ φ x) →
      let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
      let g := G.limit.flow.metric (-τ)
      let v := fun x => l (e x, τ)
      let B := fun x => g.pullbackVolumeDensity e x * Real.exp (-v x) *
        ((-deriv (fun s => l (e x, s)) τ +
          (G.limit.flow.connection (-τ)).scalarCurvature (e x) - (n : ℝ) / (2 * τ)) * φ x -
          fderiv ℝ φ x ((g.pullbackCoefficients e x).inverse (fderiv ℝ v x)))
      IntegrableOn B (Metric.ball a (r / 2)) ∧
        (∫ x in Metric.ball a (r / 2), B x) ≤ 0 := by
  have hHJ := Measure.ae_ae_of_ae_prod
    (G.ae_limitReducedLength_hamiltonJacobi_coordinates P hσ l hlim q hr hα hαβ hchart)
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hHJ] with τ hτ hHJτ
  have hτpos : 0 < τ := hα.trans hτ.1
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  let O := Metric.ball a (r / 2)
  have hclosure : closure O = Metric.closedBall a (r / 2) :=
    closure_ball a (half_pos hr).ne'
  have hclose : closure O ⊆ Metric.closedBall a r := by
    rw [hclosure]
    exact Metric.closedBall_subset_closedBall (by linarith)
  have hOs : closure O ⊆ e.source := hclose.trans
    ((Metric.closedBall_subset_closedBall (by linarith)).trans hchart)
  obtain ⟨L, hL⟩ := G.reducedLengthPullback_limit_lipschitz_on_chart_cylinder
    P hσ l hlim q hr hτpos (le_refl τ) hchart
  have hu : LipschitzOnWith L (fun x => l (e x, τ)) (Metric.closedBall a r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using
      hL.dist_le_mul (x, τ) ⟨hx, le_rfl, le_rfl⟩ (y, τ) ⟨hy, le_rfl, le_rfl⟩
  intro φ hφ hφc hφO hφ0
  apply (G.limit.flow.connection (-τ)).reducedPotential_heat_weak_inequality
    e contMDiffOn_chart_symm contMDiffOn_chart Metric.isOpen_ball
    (hclosure ▸ isCompact_closedBall _ _) hOs (hu.mono hclose) τ hHJτ
    (fun ψ hψ hψc hψO hψ0 =>
      (G.limitReducedLength_second_weak_coordinate_gradient_inequality
        P hσ l hlim q hr hτpos hchart hψ hψc hψO hψ0).2) hφ hφc hφO hφ0

end PoincareConjecture.AncientCompactTimeConvergence
