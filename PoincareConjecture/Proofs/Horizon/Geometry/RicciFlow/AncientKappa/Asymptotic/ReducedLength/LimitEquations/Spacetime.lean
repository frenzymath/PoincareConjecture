import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.LimitEquations.ActualSlice
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.LimitEquations.Exponential.Spacetime


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal
open Poincare.Analysis.Parabolic.WeakRegularity

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



theorem limitReducedLength_normalized_exp_neg_heat_pairing_nonpos
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop
        (univ ×ˢ Ioi (0 : ℝ)))
    (q : G.limit.carrier.carrier) {a : EuclideanSpace ℝ (Fin n)} {r α β : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hαβ : α ≤ β)
    (hchart : Metric.closedBall a (2 * r) ⊆
      (chartAt (EuclideanSpace ℝ (Fin n)) q).target)
    {φ : Spacetime n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ Metric.ball a (r / 2) ×ˢ Ioo α β)
    (hφ0 : ∀ z, 0 ≤ φ z) :
    let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
    let B := fun z : Spacetime n =>
      (G.limit.flow.metric (-z.2)).pullbackVolumeDensity e z.1 *
        (z.2 ^ (-(n : ℝ) / 2) * Real.exp (-l (e z.1, z.2))) *
          (-Canonical.timeDeriv φ z - (G.limit.flow.connection (-z.2)).laplacian
            (fun y => φ (e.symm y, z.2)) (e z.1))
    IntegrableOn B (Metric.ball a (r / 2) ×ˢ Ioo α β) ∧
      (∫ z in Metric.ball a (r / 2) ×ˢ Ioo α β, B z) ≤ 0 := by
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  let O := Metric.ball a (r / 2)
  have hclosure : closure O = Metric.closedBall a (r / 2) :=
    closure_ball a (half_pos hr).ne'
  have hclose : closure O ⊆ Metric.closedBall a r := by
    rw [hclosure]
    exact Metric.closedBall_subset_closedBall (by linarith)
  have hCdomain : closure O ×ˢ Icc α β ⊆
      RicciFlow.BackwardCoordinates.domain (Iio (0 : ℝ)) e := by
    rw [RicciFlow.BackwardCoordinates.domain_Iio_zero]
    intro z hz
    exact ⟨hchart ((Metric.closedBall_subset_closedBall (by linarith)) (hclose hz.1)),
      hα.trans_le hz.2.1⟩
  obtain ⟨L, hL⟩ := G.reducedLengthPullback_limit_lipschitz_on_chart_cylinder
    P hσ l hlim q hr hα hαβ hchart
  have hu : LipschitzOnWith L (fun z : Spacetime n => l (e z.1, z.2))
      (closure O ×ˢ Icc α β) := hL.mono (Set.prod_mono hclose Subset.rfl)
  apply RicciFlow.BackwardCoordinates.normalized_exp_neg_heat_pairing_nonpos
    G.limit.flow e contMDiffOn_chart_symm contMDiffOn_chart Metric.isOpen_ball
    (hclosure ▸ isCompact_closedBall _ _)
    (hclosure ▸ convex_closedBall _ _) hα hCdomain hu ?_ hφ hφc hφU hφ0
  filter_upwards [G.ae_limitReducedLength_heat_weak_coordinate_gradient
    P hσ l hlim q hr hα hαβ hchart] with τ hτ
  intro ψ hψ hψc hψO hψ0
  exact (hτ ψ hψ hψc hψO hψ0).2

end PoincareConjecture.AncientCompactTimeConvergence
