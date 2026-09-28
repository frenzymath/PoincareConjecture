import PoincareConjecture.Proofs.M08.ChartEulerCoefficients
import PoincareConjecture.Proofs.M08.ChartStationarity
import PoincareConjecture.Proofs.M08.BackwardEulerTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local instance chartEulerEquationInstance1 : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance chartEulerEquationInstance2 : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance chartEulerEquationInstance3 :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance chartEulerEquationInstance4 :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem chart_curve_contDiffOn {I : Set ℝ} (x : M) (α : ℝ → M)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α I)
    (hsrc : MapsTo α I (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    ContDiffOn ℝ ∞ ((extChartAt (𝓡 n) x) ∘ α) I := by
  apply ContMDiffOn.contDiffOn
  apply (contMDiffOn_extChartAt (I := 𝓡 n) (x := x)).comp hα
  intro r hr
  simpa only [mem_preimage, extChartAt_source] using hsrc hr

noncomputable def chartVelocityExtension {I : Set ℝ} (hI : IsOpen I)
    (x : M) (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α I)
    (hsrc : MapsTo α I (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    ParametricAlongCurveExtensionOn I α (curveVelocityWithin (n := n) α I) := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let u := (extChartAt (𝓡 n) x) ∘ α
  have hu : ContDiffOn ℝ ∞ u I := chart_curve_contDiffOn x α hα hsrc
  have hq : ContDiffOn ℝ ∞ (deriv u) I := hu.deriv_of_isOpen hI (by simp)
  refine parametricExtensionInChart e (deriv u) hI Subset.rfl hsrc hq.contMDiffOn ?_
  intro s hs
  change e.symm (α s) (deriv ((extChartAt (𝓡 n) x) ∘ α) s) = _
  rw [← e.symmL_apply (R := ℝ) (hsrc hs), chart_deriv_eq_velocity (hsrc hs)
    (((hα s hs).contMDiffAt (hI.mem_nhds hs)).mdifferentiableAt (by simp)),
    e.symmL_continuousLinearMapAt (hsrc hs)]
  simp only [curveVelocityWithin, curveVelocity, mfderivWithin_of_mem_nhds (hI.mem_nhds hs)]

theorem chartVelocityExtension_apply {I : Set ℝ} (hI : IsOpen I)
    (x : M) (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α I)
    (hsrc : MapsTo α I (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (s : ℝ) {y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    (chartVelocityExtension hI x α hα hsrc).extension s y =
      chartFrame x (deriv ((extChartAt (𝓡 n) x) ∘ α) s) y := by
  exact (Bundle.Trivialization.symmL_apply (R := ℝ)
    (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x) hy _).symm

theorem chartVelocityExtension_deriv {I : Set ℝ} (hI : IsOpen I)
    (x : M) (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α I)
    (hsrc : MapsTo α I (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ I) {y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    deriv (fun r ↦ (chartVelocityExtension hI x α hα hsrc).extension r y) s =
      chartFrame x (deriv (deriv ((extChartAt (𝓡 n) x) ∘ α)) s) y := by
  let : NormedAddCommGroup (TangentSpace (𝓡 n) y) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  let : NormedSpace ℝ (TangentSpace (𝓡 n) y) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let u := (extChartAt (𝓡 n) x) ∘ α
  have hu : ContDiffOn ℝ ∞ u I := chart_curve_contDiffOn x α hα hsrc
  have hq : ContDiffOn ℝ ∞ (deriv u) I := hu.deriv_of_isOpen hI (by simp)
  have hqd := ((hq s hs).contDiffAt (hI.mem_nhds hs)).differentiableAt (by simp)
  have heq : (fun r ↦ (chartVelocityExtension hI x α hα hsrc).extension r y) =
      fun r ↦ e.symmL ℝ y (deriv u r) :=
    funext (fun r ↦ chartVelocityExtension_apply hI x α hα hsrc r hy)
  rw [heq]
  exact ((e.symmL ℝ y).hasFDerivAt.comp_hasDerivAt s hqd.hasDerivAt).deriv

theorem chartVelocityExtension_pullback {J I : Set ℝ} (F : RicciFlow n M J)
    (time : ℝ → ℝ) (hI : IsOpen I)
    (x : M) (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α I)
    (hsrc : MapsTo α I (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ I) :
    pullbackCovariantDerivative F time α (curveVelocityWithin (n := n) α I) I
      (chartVelocityExtension hI x α hα hsrc) s =
      chartFrame x (deriv (deriv ((extChartAt (𝓡 n) x) ∘ α)) s) (α s) +
        (F.connection (time s)).connection
          (chartFrame x (deriv ((extChartAt (𝓡 n) x) ∘ α) s)) (α s)
          (chartFrame x (deriv ((extChartAt (𝓡 n) x) ∘ α) s) (α s)) := by
  let E := chartVelocityExtension hI x α hα hsrc
  let q := deriv ((extChartAt (𝓡 n) x) ∘ α)
  have heq : E.extension s =ᶠ[𝓝 (α s)] chartFrame x (q s) := by
    filter_upwards [(chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds (hsrc hs)]
      with y hy
    exact chartVelocityExtension_apply hI x α hα hsrc s hy
  have hE := (parametricExtension_contMDiffAt_space E (E.graph_mem s hs)).mdifferentiableAt
    (by simp)
  have hframe := ((chartFrame_contMDiffOn x (q s) (α s) (hsrc hs)).contMDiffAt
    ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds (hsrc hs))).mdifferentiableAt
      (by simp)
  have hcov := (F.connection (time s)).connection.isCovariantDerivativeOn.congr_of_eventuallyEq
    hE hframe univ_mem heq
  have hvel : curveVelocityWithin (n := n) α I s = chartFrame x (q s) (α s) :=
    (E.agrees s hs).symm.trans (chartVelocityExtension_apply hI x α hα hsrc s (hsrc hs))
  unfold pullbackCovariantDerivative
  rw [chartVelocityExtension_deriv hI x α hα hsrc hs (hsrc hs), hcov, hvel]

set_option maxHeartbeats 800000 in
theorem chart_momentum_regularized_equation {J I : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (hI : IsOpen I)
    (x : M) (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α I)
    (hsrc : MapsTo α I (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ I) (ht : T - s ^ 2 ∈ interior J)
    (hmomentum :
      HasDerivAt (fun r ↦ chartMomentumVector
        (chartActionMetric F T x (r, extChartAt (𝓡 n) x (α r)))
        (deriv ((extChartAt (𝓡 n) x) ∘ α) r))
        (chartForceVector
          (spatialFDeriv (chartActionMetric F T x) (s, extChartAt (𝓡 n) x (α s)))
          (spatialFDeriv (chartActionPotential F T x) (s, extChartAt (𝓡 n) x (α s)))
          (deriv ((extChartAt (𝓡 n) x) ∘ α) s)) s) :
    regularizedLGeodesicEquation F T α I (chartVelocityExtension hI x α hα hsrc) s := by
  let u := (extChartAt (𝓡 n) x) ∘ α
  let q := deriv u
  let E := chartVelocityExtension hI x α hα hsrc
  have hu : ContDiffOn ℝ ∞ u I := chart_curve_contDiffOn x α hα hsrc
  have hq : ContDiffOn ℝ ∞ q I := hu.deriv_of_isOpen hI (by simp)
  have hud := ((hu s hs).contDiffAt (hI.mem_nhds hs)).differentiableAt (by simp)
  have hqd := ((hq s hs).contDiffAt (hI.mem_nhds hs)).differentiableAt (by simp)
  intro W
  let z := (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).continuousLinearMapAt
    ℝ (α s) W
  have hW : chartFrame x z (α s) = W :=
    Bundle.Trivialization.symmL_continuousLinearMapAt
      (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x) (hsrc hs) W
  have hpair : HasDerivAt (fun r ↦ chartActionMetric F T x (r, u r) (q r) z)
      (spatialFDeriv (chartActionMetric F T x) (s, u s) z (q s) (q s) / 2 +
        spatialFDeriv (chartActionPotential F T x) (s, u s) z) s := by
    simpa only [u, q, Function.comp_def, innerSL_apply_apply,
      chartMomentumVector_inner, chartForceVector_inner]
      using ((innerSL ℝ z).hasFDerivAt.comp_hasDerivAt s hmomentum)
  have hmetric := chartActionMetric_curve_derivative F T (hsrc hs) ht hud.hasDerivAt
    hqd.hasDerivAt (rfl : u s = extChartAt (𝓡 n) x (α s)) z
  have hscalar := hmetric.unique hpair
  have hvel : curveVelocityWithin (n := n) α I s = chartFrame x (q s) (α s) :=
    (E.agrees s hs).symm.trans (chartVelocityExtension_apply hI x α hα hsrc s (hsrc hs))
  have hpot := chartActionPotential_spatial_apply F hM04 T (hsrc hs) ht z
  rw [← hW]
  unfold regularizedEulerResidual
  rw [chartVelocityExtension_pullback F (fun r ↦ T - r ^ 2) hI x α hα hsrc hs, hvel,
    map_add, ContinuousLinearMap.add_apply,
    ← chartActionMetric_apply F T (hsrc hs) s,
    chartActionMetric_connection_diagonal F T (hsrc hs) ht]
  unfold scalarCurvatureDifferential
  rw [← hpot]
  dsimp only [u, q, Function.comp_apply] at hscalar ⊢
  linarith

end PoincareConjecture.M08
