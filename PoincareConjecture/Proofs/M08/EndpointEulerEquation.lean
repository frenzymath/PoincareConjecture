import PoincareConjecture.Proofs.M08.EndpointEulerCoefficients
import PoincareConjecture.Proofs.M08.ChartEulerEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local instance endpointEulerEquationInstance1 : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance endpointEulerEquationInstance2 : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance endpointEulerEquationInstance3 :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance endpointEulerEquationInstance4 :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem curveVelocityWithin_eq_of_uniqueDiff {C U : Set ℝ} (hU : IsOpen U)
    (hCU : C ⊆ U) (hC : UniqueDiffOn ℝ C) (α : ℝ → M)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U) {s : ℝ} (hs : s ∈ C) :
    curveVelocityWithin (n := n) α C s = curveVelocityWithin (n := n) α U s := by
  unfold curveVelocityWithin
  rw [mfderivWithin_eq_mfderiv (hC s hs).uniqueMDiffWithinAt
    (((hα s (hCU hs)).contMDiffAt (hU.mem_nhds (hCU hs))).mdifferentiableAt (by simp)),
    mfderivWithin_of_mem_nhds (hU.mem_nhds (hCU hs))]

def chartVelocityExtensionWithin {C U : Set ℝ} (hU : IsOpen U)
    (hCU : C ⊆ U) (hC : UniqueDiffOn ℝ C) (x : M) (α : ℝ → M)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (hsrc : MapsTo α U (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    ParametricAlongCurveExtensionOn C α (curveVelocityWithin (n := n) α C) where
  extension := (chartVelocityExtension hU x α hα hsrc).extension
  domain := (chartVelocityExtension hU x α hα hsrc).domain
  open_domain := (chartVelocityExtension hU x α hα hsrc).open_domain
  graph_mem s hs := (chartVelocityExtension hU x α hα hsrc).graph_mem s (hCU hs)
  smooth := (chartVelocityExtension hU x α hα hsrc).smooth
  agrees s hs := ((chartVelocityExtension hU x α hα hsrc).agrees s (hCU hs)).trans
    (curveVelocityWithin_eq_of_uniqueDiff hU hCU hC α hα hs).symm

theorem chartVelocityExtensionWithin_pullback {J C U : Set ℝ} (F : RicciFlow n M J)
    (time : ℝ → ℝ) (hU : IsOpen U) (hCU : C ⊆ U) (hC : UniqueDiffOn ℝ C)
    (x : M) (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (hsrc : MapsTo α U (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C) :
    pullbackCovariantDerivative F time α (curveVelocityWithin (n := n) α C) C
      (chartVelocityExtensionWithin hU hCU hC x α hα hsrc) s =
      chartFrame x (deriv (deriv ((extChartAt (𝓡 n) x) ∘ α)) s) (α s) +
        (F.connection (time s)).connection
          (chartFrame x (deriv ((extChartAt (𝓡 n) x) ∘ α) s)) (α s)
          (chartFrame x (deriv ((extChartAt (𝓡 n) x) ∘ α) s) (α s)) := by
  have h := chartVelocityExtension_pullback F time hU x α hα hsrc (hCU hs)
  unfold pullbackCovariantDerivative chartVelocityExtensionWithin
  rw [curveVelocityWithin_eq_of_uniqueDiff hU hCU hC α hα hs]
  exact h

set_option maxHeartbeats 1000000 in
theorem closed_chart_momentum_regularized_equation {J C U : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ)
    (hU : IsOpen U) (hCU : C ⊆ U) (hC : UniqueDiffOn ℝ C)
    (x : M) (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (hsrc : MapsTo α U (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (htime : ∀ r ∈ C, T - r ^ 2 ∈ J) {s : ℝ} (hs : s ∈ C)
    (hmomentum : HasDerivWithinAt (fun r ↦ chartMomentumVector
        (chartActionMetric F T x (r, extChartAt (𝓡 n) x (α r)))
        (deriv ((extChartAt (𝓡 n) x) ∘ α) r))
      (chartForceVector
        (spatialWithinFDeriv C (extChartAt (𝓡 n) x).target (chartActionMetric F T x)
          (s, extChartAt (𝓡 n) x (α s)))
        (spatialWithinFDeriv C (extChartAt (𝓡 n) x).target (chartActionPotential F T x)
          (s, extChartAt (𝓡 n) x (α s)))
        (deriv ((extChartAt (𝓡 n) x) ∘ α) s)) C s) :
    regularizedLGeodesicEquation F T α C
      (chartVelocityExtensionWithin hU hCU hC x α hα hsrc) s := by
  let u := (extChartAt (𝓡 n) x) ∘ α
  let q := deriv u
  let E := chartVelocityExtensionWithin hU hCU hC x α hα hsrc
  have hu : ContDiffOn ℝ ∞ u U := chart_curve_contDiffOn x α hα hsrc
  have hq : ContDiffOn ℝ ∞ q U := hu.deriv_of_isOpen hU (by simp)
  have hud := ((hu s (hCU hs)).contDiffAt (hU.mem_nhds (hCU hs))).differentiableAt (by simp)
  have hqd := ((hq s (hCU hs)).contDiffAt (hU.mem_nhds (hCU hs))).differentiableAt (by simp)
  have htarget : MapsTo u C (extChartAt (𝓡 n) x).target := by
    intro r hr
    apply (extChartAt (𝓡 n) x).map_source
    simpa only [extChartAt_source] using hsrc (hCU hr)
  intro W
  let z := (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).continuousLinearMapAt
    ℝ (α s) W
  have hW : chartFrame x z (α s) = W :=
    Bundle.Trivialization.symmL_continuousLinearMapAt
      (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x) (hsrc (hCU hs)) W
  have hpair : HasDerivWithinAt (fun r ↦ chartActionMetric F T x (r, u r) (q r) z)
      (spatialWithinFDeriv C (extChartAt (𝓡 n) x).target (chartActionMetric F T x)
          (s, u s) z (q s) (q s) / 2 +
        spatialWithinFDeriv C (extChartAt (𝓡 n) x).target (chartActionPotential F T x)
          (s, u s) z) C s := by
    simpa only [u, q, Function.comp_def, innerSL_apply_apply,
      chartMomentumVector_inner, chartForceVector_inner]
      using ((innerSL ℝ z).hasFDerivAt.comp_hasDerivWithinAt s hmomentum)
  have hmetric := chartActionMetric_closed_curve_derivative F T htime (hsrc (hCU hs)) hs
    (hC s hs) hud.hasDerivAt hqd.hasDerivAt (rfl : u s = extChartAt (𝓡 n) x (α s)) htarget z
  have hscalar := (hmetric.derivWithin (hC s hs)).symm.trans (hpair.derivWithin (hC s hs))
  have hvel : curveVelocityWithin (n := n) α C s = chartFrame x (q s) (α s) :=
    (E.agrees s hs).symm.trans
      (chartVelocityExtension_apply hU x α hα hsrc s (hsrc (hCU hs)))
  have hpot := chartActionPotential_closed_spatial_apply F hM04 T htime (hsrc (hCU hs)) hs z
  rw [← hW]
  unfold regularizedEulerResidual
  rw [chartVelocityExtensionWithin_pullback F (fun r ↦ T - r ^ 2) hU hCU hC x α hα hsrc hs,
    hvel, map_add, add_apply, ← chartActionMetric_apply F T (hsrc (hCU hs)) s,
    chartActionMetric_closed_connection_diagonal F T htime (hsrc (hCU hs)) hs]
  unfold scalarCurvatureDifferential
  rw [← hpot]
  dsimp only [u, q, Function.comp_apply] at hscalar ⊢
  linarith

set_option maxHeartbeats 800000 in
theorem closed_phase_momentum_of_eqOn {J C U : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (x : M) (hU : IsOpen U) (hCU : C ⊆ U) (hC : UniqueDiffOn ℝ C)
    (u v Pbar : ℝ → EuclideanSpace ℝ (Fin n))
    (hv : ContDiffOn ℝ ∞ v U) (hvu : EqOn v u C)
    (htarget : MapsTo u C (extChartAt (𝓡 n) x).target)
    (hphase : ∀ s ∈ C, HasDerivWithinAt (fun r ↦ (u r, Pbar r))
      (closedChartEulerPhase F T x C s (u s, Pbar s)) C s) :
    ∀ s ∈ C, HasDerivWithinAt
      (fun r ↦ chartMomentumVector (chartActionMetric F T x (r, v r)) (deriv v r))
      (chartForceVector
        (spatialWithinFDeriv C (extChartAt (𝓡 n) x).target (chartActionMetric F T x) (s, v s))
        (spatialWithinFDeriv C (extChartAt (𝓡 n) x).target (chartActionPotential F T x) (s, v s))
        (deriv v s)) C s := by
  have hderiv (s : ℝ) (hs : s ∈ C) :
      deriv v s = Ring.inverse (chartMetricOperator F T x (s, u s)) (Pbar s) := by
    have hud : HasDerivWithinAt u
        (Ring.inverse (chartMetricOperator F T x (s, u s)) (Pbar s)) C s := (hphase s hs).fst
    have hvd : HasDerivWithinAt v (deriv v s) C s :=
      (((hv s (hCU hs)).contDiffAt (hU.mem_nhds (hCU hs))).differentiableAt
      (by simp)).hasDerivAt.hasDerivWithinAt
    exact (hvd.derivWithin (hC s hs)).symm.trans
      ((hud.congr_of_mem hvu hs).derivWithin (hC s hs))
  have hmomentum : EqOn
      (fun r ↦ chartMomentumVector (chartActionMetric F T x (r, v r)) (deriv v r)) Pbar C := by
    intro s hs
    change chartMetricOperator F T x (s, v s) (deriv v s) = Pbar s
    rw [hvu hs, hderiv s hs]
    exact congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) ↦ A (Pbar s))
      (Ring.mul_inverse_cancel _ (chartMetricOperator_isUnit_of_target F T x (htarget hs)))
  intro s hs
  have hPd : HasDerivWithinAt Pbar
      (chartForceVector
        (spatialWithinFDeriv C (extChartAt (𝓡 n) x).target (chartActionMetric F T x) (s, u s))
        (spatialWithinFDeriv C (extChartAt (𝓡 n) x).target (chartActionPotential F T x) (s, u s))
        (Ring.inverse (chartMetricOperator F T x (s, u s)) (Pbar s))) C s := (hphase s hs).snd
  rw [← hderiv s hs, ← hvu hs] at hPd
  exact hPd.congr_of_mem hmomentum hs

end PoincareConjecture.M08
