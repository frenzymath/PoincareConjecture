import PoincareConjecture.Proofs.M30.Thm11_1.TerminalComponentGeometry
import PoincareConjecture.Proofs.M30.Thm1_34.LocalVolume
import PoincareConjecture.Proofs.M04.TensorNorm

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M30

open RiemannianMetric

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

theorem exists_terminalComponent_local_geometry
    (hC : RicciFlowCurvatureTheory.{u}) {S : GeneralizedBlowupSequence.{u}}
    {epsilon canonicalConstant kappa r₀ mu : ℝ}
    (H : M30CommonBlowupControls S epsilon canonicalConstant kappa r₀ mu)
    (hbound : GeneralizedBlowupBoundedDistance S) :
    ∃ K vlower Vupper : ℕ → ℝ,
      (∀ j, 0 ≤ K j) ∧ (∀ j, 0 < vlower j) ∧ (∀ j, 0 ≤ Vupper j) ∧
      ∀ j : ℕ, ∀ᶠ k in atTop,
        IsCompact (closure ((terminalComponentMetric S k).ball
          (terminalComponentBase S k) ((j : ℝ) + 3))) ∧
        (∀ x ∈ (terminalComponentMetric S k).ball
            (terminalComponentBase S k) ((j : ℝ) + 3),
          (terminalComponentMetric S k).leviCivitaData.curvatureTensorNorm x ≤ K j) ∧
        (∀ q ∈ (terminalComponentMetric S k).ball
            (terminalComponentBase S k) ((j : ℝ) + 1),
          ENNReal.ofReal (vlower j) ≤ (terminalComponentMetric S k).volumeMeasure
            ((terminalComponentMetric S k).ball q 1)) ∧
        (terminalComponentMetric S k).volumeMeasure
            ((terminalComponentMetric S k).ball (terminalComponentBase S k) ((j : ℝ) + 3)) ≤
          ENNReal.ofReal (Vupper j) := by
  obtain ⟨rho, v, hrho, hv, hvolume⟩ :=
    exists_eventually_terminalComponent_volume_lower_bound hC H hbound
  let a (j : ℕ) : ℝ := (j : ℝ) + 3
  have ha (j : ℕ) : 0 < a j := by dsimp [a]; positivity
  have hbig (j : ℕ) : a j < 3 * a j + 2 * rho := by linarith [ha j]
  choose K hK hderiv using fun j =>
    eventually_terminalComponent_curvatureDerivativeNorm_le hC H hbound
      (3 * a j + 2 * rho) ((ha j).trans (hbig j)) 0
  let vlower (j : ℕ) := smallerBallVolumeBound 3 (K j) (a j + rho) v 1
  let Vupper (j : ℕ) := modelVolume 3 (K j) (a j)
  refine ⟨K, vlower, Vupper, fun j => (hK j).le, ?_, ?_, ?_⟩
  · intro j
    exact smallerBallVolumeBound_pos (by norm_num) (hK j).le
      (add_pos (ha j) hrho) hv zero_lt_one
  · intro j
    exact (modelVolume_pos (by norm_num) (hK j).le (ha j)).le
  · intro j
    filter_upwards [hvolume, hderiv j,
      eventually_terminalComponent_compact_ball H
        (3 * a j + 2 * rho) ((ha j).trans (hbig j))] with k hkvol hkderiv hkcompact
    let g := terminalComponentMetric S k
    let D := g.leviCivitaData
    let p := terminalComponentBase S k
    have hkcurv : ∀ x ∈ g.ball p (3 * a j + 2 * rho), D.curvatureTensorNorm x ≤ K j := by
      intro x hx
      simpa only [LeviCivitaData.curvatureDerivativeNorm_zero] using hkderiv x hx
    have hsub : g.ball p (a j) ⊆ g.ball p (3 * a j + 2 * rho) :=
      fun _ hx => hx.trans_le (ENNReal.ofReal_le_ofReal (hbig j).le)
    refine ⟨hkcompact.of_isClosed_subset isClosed_closure (closure_mono hsub),
      fun x hx => hkcurv x (hsub hx), ?_, ?_⟩
    · intro q hq
      have hqa : q ∈ g.ball p (a j) := hq.trans_le
        (ENNReal.ofReal_le_ofReal (by dsimp [a]; linarith))
      exact ((local_volume_bounds_of_base_volume g D p (by norm_num) (ha j) hrho hv
        (hK j).le hkcompact hkcurv hkvol zero_lt_one
        (by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) j])).2 q hqa).1
    · exact volume_upper_of_precompact_ball g p (by norm_num)
        ((ha j).trans (hbig j)) (hK j).le hkcompact D
        (fun x hx w => D.ricci_quadratic_lower_bound_of_curvatureTensorNorm_le
          x (hkcurv x hx) w) (ha j) (hbig j)

end PoincareConjecture.M30
