import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Exponential.StandardPoleBalls
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Exponential.InitialExponential

/-!
# The standard exponential with the limiting initial frame

The explicit standard pole supplies a smooth global model phase solving
the actual standard geodesic equation. Morgan--Tian, Claim 16.6 and
Corollary 16.7, pp. 371-372; see
`derivations/20-exponential-model-and-convergence.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M44

local notation "E" => StandardCapSpace

/-- Every radial curve of the standard pole is a geodesic for all real
times. Source: the model in Claim 16.6, pp. 371-372. -/
theorem standardRadialExponential_isGeodesicOn (g₀ : StandardInitialMetric) (v : E) :
    g₀.metric.IsGeodesicOn (fun t : ℝ => standardRadialExponential g₀ (t • v)) univ := by
  intro t _
  let R := ‖v‖ + ‖t • v‖ + 1
  have hexp : ∀ w ∈ Metric.ball (0 : E) R, ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ γ : ℝ → E,
      g₀.metric.IsGeodesicOn γ (Ioo (-epsilon) (1 + epsilon)) ∧ γ 0 = 0 ∧
      HasDerivAt (fun s => extChartAt (𝓡 3) (0 : E) (γ s))
        ((ContinuousLinearEquiv.refl ℝ E) w) 0 ∧
      γ 1 = standardRadialExponential g₀ w := by
    intro w _
    simpa only [StandardCapSpace, extChartAt_self_eq, modelWithCornersSelf_coe,
      id_eq, ContinuousLinearEquiv.refl_apply] using exists_standard_radial_geodesic g₀ w
  apply g₀.metric.isGeodesicOn_radial_of_initial_data 0 (ContinuousLinearEquiv.refl ℝ E)
    (standardRadialExponential g₀) hexp (v := v)
  · simp only [Metric.mem_ball, dist_zero_right, R]
    linarith [norm_nonneg (t • v)]
  · simp only [mem_ofPred_eq, Metric.mem_ball, dist_zero_right, R]
    linarith [norm_nonneg v]

/-- The standard exponential expressed in a fixed initial frame.
Source: Corollary 16.7, p. 372. -/
noncomputable def standardFrameExponential (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E) :
    E → E := standardRadialExponential g₀ ∘ L

/-- The fixed-frame model endpoint is globally smooth.
Source: Claim 16.6, pp. 371-372. -/
theorem standardFrameExponential_contDiff (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E) :
    ContDiff ℝ ∞ (standardFrameExponential g₀ L) :=
  (standardRadialExponential_contDiff g₀).comp L.contDiff

/-- The fixed-frame model endpoint fixes the tip.
Source: Claim 16.6, pp. 371-372. -/
theorem standardFrameExponential_zero (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E) :
    standardFrameExponential g₀ L 0 = 0 := by
  simp only [standardFrameExponential, Function.comp_apply, map_zero,
    standardRadialExponential_zero]

/-- The derivative of the model endpoint at zero is the fixed frame.
Source: Corollary 16.7, p. 372. -/
theorem standardFrameExponential_hasFDerivAt_zero
    (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E) :
    HasFDerivAt (standardFrameExponential g₀ L) L.toContinuousLinearMap 0 := by
  have hd : HasFDerivAt (standardRadialExponential g₀) (ContinuousLinearMap.id ℝ E) (L 0) :=
    by simpa only [map_zero] using standardRadialExponential_hasFDerivAt_zero g₀
  simpa only [standardFrameExponential, ContinuousLinearMap.id_comp] using
    hd.comp 0 L.hasFDerivAt

/-- The actual position and radial velocity of the fixed model.
Source: Claim 16.6, pp. 371-372. -/
noncomputable def standardFramePhase (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E)
    (z : E × ℝ) : E × E :=
  (standardFrameExponential g₀ L (z.2 • z.1),
    fderiv ℝ (standardFrameExponential g₀ L) (z.2 • z.1) z.1)

/-- The model phase is jointly smooth with no parameter or time
restriction. Source: Claim 16.6, pp. 371-372. -/
theorem standardFramePhase_contDiff (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E) :
    ContDiff ℝ ∞ (standardFramePhase g₀ L) := by
  have he := standardFrameExponential_contDiff g₀ L
  have harg : ContDiff ℝ ∞ (fun z : E × ℝ => z.2 • z.1) := by fun_prop
  exact (he.comp harg).prodMk
    (((he.fderiv_right (m := ∞) (by simp)).comp harg).clm_apply contDiff_fst)

/-- The displayed model velocity is its actual time derivative.
Source: Claim 16.6, pp. 371-372. -/
theorem standardFramePhase_eq_curve_velocity
    (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E) (v : E) (t : ℝ) :
    standardFramePhase g₀ L (v, t) =
      (standardFrameExponential g₀ L (t • v),
        deriv (fun s => standardFrameExponential g₀ L (s • v)) t) := by
  have hd := ((standardFrameExponential_contDiff g₀ L).differentiable (by simp)
    (t • v)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const v)
  refine Prod.ext rfl ?_
  simpa only [standardFramePhase, Function.comp_def, id_eq, one_smul] using hd.deriv.symm

/-- The actual initial phase data use the limiting frame.
Source: Corollary 16.7, p. 372. -/
theorem standardFramePhase_initial (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E) (v : E) :
    standardFramePhase g₀ L (v, 0) = (0, L v) := by
  simp only [standardFramePhase, zero_smul, standardFrameExponential_zero,
    (standardFrameExponential_hasFDerivAt_zero g₀ L).fderiv,
    ContinuousLinearEquiv.coe_coe]

/-- The actual model phase satisfies the fixed standard geodesic field,
including both endpoints of every comparison interval.
Source: Claim 16.6, pp. 371-372. -/
theorem standardFramePhase_hasDerivAt (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E)
    (v : E) (t : ℝ) :
    HasDerivAt (fun s => standardFramePhase g₀ L (v, s))
      (coordinateGeodesicField g₀.metric.euclideanCoefficients
        (standardFramePhase g₀ L (v, t))) t := by
  have hgeo : g₀.metric.IsGeodesicOn
      (fun s => standardFrameExponential g₀ L (s • v)) univ := by
    simpa only [standardFrameExponential, Function.comp_apply, map_smul] using
      standardRadialExponential_isGeodesicOn g₀ (L v)
  have hphase := hgeo.hasDerivAt_chart_at (t := t) (mem_univ t) (0 : E)
    (by simp [StandardCapSpace])
  simp only [StandardCapSpace, extChartAt_self_eq, modelWithCornersSelf_coe,
    id_eq] at hphase
  have hcoeff : g₀.metric.pullbackCoefficients (extChartAt (𝓡 3) (0 : E)).symm =
      g₀.metric.euclideanCoefficients := by
    ext x a b
    simp [StandardCapSpace, RiemannianMetric.pullbackCoefficients,
      RiemannianMetric.euclideanCoefficients]
    rfl
  rw [hcoeff] at hphase
  have heq : (fun s => standardFramePhase g₀ L (v, s)) =
      (fun s => (standardFrameExponential g₀ L (s • v),
        deriv (fun u => standardFrameExponential g₀ L (u • v)) s)) := by
    funext s
    exact standardFramePhase_eq_curve_velocity g₀ L v s
  rw [heq, standardFramePhase_eq_curve_velocity]
  exact hphase.1.prodMk hphase.2

end PoincareMT.M44
