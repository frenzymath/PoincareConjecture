import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.LimitEquations.Spacetime
import PoincareConjecture.Proofs.Horizon.Analysis.Distribution.LocalNonpositive
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.TestOperator


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000

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



theorem limitReducedLength_heat_pairing_nonpos_on_chart
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop
        (univ ×ˢ Ioi (0 : ℝ)))
    (q : G.limit.carrier.carrier)
    {φ : Spacetime n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target ×ˢ Ioi (0 : ℝ))
    (hφ0 : ∀ z, 0 ≤ φ z) :
    let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
    let B := fun z : Spacetime n =>
      (G.limit.flow.metric (-z.2)).pullbackVolumeDensity e z.1 *
        (z.2 ^ (-(n : ℝ) / 2) * Real.exp (-l (e z.1, z.2))) *
          (-Canonical.timeDeriv φ z - (G.limit.flow.connection (-z.2)).laplacian
            (fun y => φ (e.symm y, z.2)) (e z.1))
    IntegrableOn B (e.source ×ˢ Ioi (0 : ℝ)) ∧
      (∫ z in e.source ×ˢ Ioi (0 : ℝ), B z) ≤ 0 := by
  let F := G.limit.flow
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  let D := e.source ×ˢ Ioi (0 : ℝ)
  let w := fun z : Spacetime n => (F.metric (-z.2)).pullbackVolumeDensity e z.1 *
    (z.2 ^ (-(n : ℝ) / 2) * Real.exp (-l (e z.1, z.2)))
  let a := RicciFlow.BackwardCoordinates.principal F e
  let b := RicciFlow.BackwardCoordinates.drift F e
  let A := fun ψ z => w z * Canonical.diffusionTest a b ψ z
  have hD : IsOpen D := e.open_source.prod isOpen_Ioi
  have hop (ψ : Spacetime n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (z : Spacetime n)
      (hz : z ∈ D) : Canonical.diffusionTest a b ψ z =
      -Canonical.timeDeriv ψ z - (F.connection (-z.2)).laplacian
        (fun y => ψ (e.symm y, z.2)) (e z.1) := by
    have hz' : z ∈ RicciFlow.BackwardCoordinates.domain (Iio (0 : ℝ)) e := by
      simpa only [RicciFlow.BackwardCoordinates.domain_Iio_zero] using hz
    exact (Canonical.forwardCoefficients_adjoint
      (RicciFlow.BackwardCoordinates.isOpen_domain e)
      (RicciFlow.BackwardCoordinates.contDiffOn_principal F e
        contMDiffOn_chart_symm contMDiffOn_chart)
      (RicciFlow.BackwardCoordinates.contDiffOn_drift F e
        contMDiffOn_chart_symm contMDiffOn_chart) hψ.contDiffOn hz').symm.trans
        (RicciFlow.BackwardCoordinates.forwardCoefficients_adjoint_eq_coordinateLaplacian
          F e contMDiffOn_chart_symm contMDiffOn_chart hψ hz')
  have hadd : ∀ f g : Spacetime n → ℝ, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      A (fun z => f z + g z) = fun z => A f z + A g z := by
    intro f g hf hg
    funext z
    change w z * Canonical.diffusionTest a b (fun y => f y + g y) z = _
    rw [Canonical.diffusionTest_add a b hf hg]
    exact mul_add _ _ _
  have hzero : ∀ f : Spacetime n → ℝ, ContDiff ℝ ∞ f →
      ∀ z ∉ tsupport f, A f z = 0 := by
    intro f _ z hz
    change w z * Canonical.diffusionTest a b f z = 0
    rw [Canonical.diffusionTest_eq_zero_of_notMem_tsupport a b f hz, mul_zero]
  have hlocal : ∀ z ∈ D, ∃ U : Set (Spacetime n), IsOpen U ∧ z ∈ U ∧ U ⊆ D ∧
      ∀ ψ : Spacetime n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ U → (∀ y, 0 ≤ ψ y) →
        IntegrableOn (A ψ) U ∧ (∫ y in U, A ψ y) ≤ 0 := by
    intro z hz
    obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp e.open_source z.1 hz.1
    let r := R / 4
    have hr : 0 < r := by dsimp only [r]; positivity
    have hchart : Metric.closedBall z.1 (2 * r) ⊆ e.source := by
      intro x hx
      apply hball
      have hd : dist x z.1 ≤ 2 * r := hx
      change dist x z.1 < R
      dsimp only [r] at hd
      linarith
    let U := Metric.ball z.1 (r / 2) ×ˢ Ioo (z.2 / 2) (z.2 + 1)
    have hU : IsOpen U := Metric.isOpen_ball.prod isOpen_Ioo
    have hUD : U ⊆ D := by
      intro y hy
      exact ⟨hchart ((Metric.closedBall_subset_closedBall (by linarith))
        (Metric.ball_subset_closedBall hy.1)), by
          have hzt : 0 < z.2 := hz.2
          have hyt : z.2 / 2 < y.2 := hy.2.1
          exact (half_pos hzt).trans hyt⟩
    refine ⟨U, hU, ⟨Metric.mem_ball_self (half_pos hr), ?_, ?_⟩, hUD, ?_⟩
    · exact half_lt_self hz.2
    · linarith
    · intro ψ hψ hψc hψU hψ0
      obtain ⟨hi, hw⟩ := G.limitReducedLength_normalized_exp_neg_heat_pairing_nonpos
        P hσ l hlim q hr (half_pos hz.2)
          (by have hzt : 0 < z.2 := hz.2; linarith) hchart hψ hψc hψU hψ0
      have heq : ∀ y ∈ U, A ψ y = w y *
          (-Canonical.timeDeriv ψ y - (F.connection (-y.2)).laplacian
            (fun x => ψ (e.symm x, y.2)) (e y.1)) := by
        intro y hy
        exact congrArg (w y * ·) (hop ψ hψ y (hUD hy))
      refine ⟨hi.congr_fun (fun y hy => (heq y hy).symm) hU.measurableSet, ?_⟩
      rw [setIntegral_congr_fun hU.measurableSet heq]
      exact hw
  obtain ⟨hi, hw⟩ := Poincare.Analysis.integrableOn_integral_nonpos_of_locally_test_nonpos
    volume A hadd hzero hlocal hφ hφc hφD hφ0
  have heq : ∀ z ∈ D, A φ z = w z *
      (-Canonical.timeDeriv φ z - (F.connection (-z.2)).laplacian
        (fun y => φ (e.symm y, z.2)) (e z.1)) :=
    fun z hz => congrArg (w z * ·) (hop φ hφ z hz)
  exact ⟨hi.congr_fun heq hD.measurableSet,
    (setIntegral_congr_fun hD.measurableSet heq) ▸ hw⟩

end PoincareConjecture.AncientCompactTimeConvergence
