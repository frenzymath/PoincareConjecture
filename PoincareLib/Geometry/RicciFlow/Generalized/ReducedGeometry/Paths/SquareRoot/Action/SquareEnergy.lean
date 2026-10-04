import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.SquareRoot.Action.SquarePullback
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.SquareRoot.Action.SquareRootAction
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Density.InteriorDensity

/-!
# Finite square-time energy of every admissible generalized path

Morgan-Tian equations (6.1)-(6.2) and Lemma 6.8, pp. 106, 108-109.
Compact-path scalar integrability separates kinetic energy from the
actual action. Square substitution removes its singular weight without
assuming minimality, the Euler equation or endpoint derivatives.
-/

set_option autoImplicit false
-- The scalar tangent model and the supplied horizontal fibers retain their actual operations.
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)

include p in
/-- Squaring a closed square-time parameter stays in the actual
original path interval, equation (6.2), p. 106. -/
theorem squarePath_parameter_mem {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    s ^ 2 ∈ Icc τ₁ τ₂ := by
  have hsnonneg := (Real.sqrt_nonneg τ₁).trans hs.1
  constructor
  · simpa only [Real.sq_sqrt p.tau_nonneg] using
      (sq_le_sq₀ (Real.sqrt_nonneg τ₁) hsnonneg).mpr hs.1
  · simpa only [Real.sq_sqrt (p.tau_nonneg.trans p.tau_lt.le)] using
      (sq_le_sq₀ hsnonneg (Real.sqrt_nonneg τ₂)).mpr hs.2

/-- Every admissible path is continuous in square time on its full
closed interval, including initial time zero, equation (6.2), p. 106. -/
theorem squarePath_continuousOn : ContinuousOn (fun s => p.curve (s ^ 2))
    (M14SqrtParameterInterval τ₁ τ₂) :=
  p.curve_continuous.comp (continuous_id.pow 2).continuousOn
    (fun _ hs => squarePath_parameter_mem p hs)

/-- Every admissible path has its actual C1 square-time curve on the
strict square interval, equation (6.2), p. 106. -/
theorem squarePath_contMDiffOn : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) 1
    (fun s => p.curve (s ^ 2)) (Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :=
  p.curve_regular.comp ((contDiff_id.pow 2).contMDiff.contMDiffOn)
    (fun _ hs => ⟨Real.lt_sq_of_sqrt_lt hs.1,
      (Real.lt_sqrt ((Real.sqrt_nonneg τ₁).trans_lt hs.1).le).mp hs.2⟩)

/-- The actual projected square-time derivative is the rescaled
original horizontal velocity on the strict interval, equation (6.2), p. 106. -/
theorem squarePath_projectedVelocity {s : ℝ}
    (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
    projectedCurveVelocity G (fun r => p.curve (r ^ 2)) s =
      (2 * s) • p.horizontal_velocity (s ^ 2) := by
  have hτ : s ^ 2 ∈ Ioo τ₁ τ₂ := ⟨Real.lt_sq_of_sqrt_lt hs.1,
    (Real.lt_sqrt ((Real.sqrt_nonneg τ₁).trans_lt hs.1).le).mp hs.2⟩
  have hγ := ((p.curve_regular _ hτ).contMDiffAt (isOpen_Ioo.mem_nhds hτ)).mdifferentiableAt
    (by simp)
  have hsq : HasDerivAt (fun r : ℝ => r ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  have hsqmf : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun r : ℝ => r ^ 2) s (1 : ℝ) =
      (2 * s) • (1 : TangentSpace (𝓘(ℝ, ℝ)) (s ^ 2)) := by
    have hv := congrArg (fun L : TangentSpace (𝓘(ℝ, ℝ)) s →L[ℝ]
      TangentSpace (𝓘(ℝ, ℝ)) (s ^ 2) => L 1) hsq.hasFDerivAt.hasMFDerivAt.mfderiv
    change mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun r : ℝ => r ^ 2) s (1 : ℝ) =
      (ContinuousLinearMap.toSpanSingleton ℝ (2 * s)) (1 : ℝ) at hv
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul, smul_eq_mul,
      mul_one, one_mul] using hv
  have hchain := mfderiv_comp_apply s (f := fun r : ℝ => r ^ 2) (g := p.curve)
    hγ hsq.differentiableAt.mdifferentiableAt (1 : ℝ)
  rw [hsqmf, map_smul] at hchain
  change G.spacetime.horizontalProjection (p.curve (s ^ 2))
    (mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) (p.curve ∘ fun r => r ^ 2) s (1 : ℝ)) = _
  rw [hchain, map_smul]
  exact congrArg (fun v => (2 * s) • v) (backwardPath_velocity_eq_projected p hτ).symm

/-- Finite actual action gives integrable weighted kinetic energy by
subtracting the continuous scalar term, equations (6.1)-(6.2), p. 106. -/
theorem backwardPath_weightedKinetic_intervalIntegrable
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) :
    IntervalIntegrable (fun t => Real.sqrt t * G.spacetime.horizontalMetric.inner (p.curve t)
      (p.horizontal_velocity t) (p.horizontal_velocity t)) MeasureTheory.volume τ₁ τ₂ := by
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  have hscalar : ContinuousOn (fun t => Real.sqrt t *
      horizontalScalarCurvature G.leafwise (p.curve t)) (Icc τ₁ τ₂) :=
    Real.continuous_sqrt.continuousOn.mul
      (H.scalar_smooth.continuous.comp_continuousOn p.curve_continuous)
  apply (p.action_integrable.sub (hscalar.intervalIntegrable_of_Icc p.tau_lt.le)).congr
  intro t _
  simp only [M14RawLIntegrand]
  ring

/-- The actual rescaled horizontal kinetic energy is integrable on the
entire square interval, the finite-energy input for Lemma 6.8, pp. 108-109. -/
theorem squarePath_kinetic_intervalIntegrable
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) :
    IntervalIntegrable (fun s => G.spacetime.horizontalMetric.inner (p.curve (s ^ 2))
      ((2 * s) • p.horizontal_velocity (s ^ 2)) ((2 * s) • p.horizontal_velocity (s ^ 2)))
      MeasureTheory.volume (Real.sqrt τ₁) (Real.sqrt τ₂) := by
  let W := fun t => Real.sqrt t * G.spacetime.horizontalMetric.inner (p.curve t)
    (p.horizontal_velocity t) (p.horizontal_velocity t)
  have hle := Real.sqrt_le_sqrt p.tau_lt.le
  have htrans : IntervalIntegrable (fun s => W (s ^ 2) * (2 * s))
      MeasureTheory.volume (Real.sqrt τ₁) (Real.sqrt τ₂) := by
    apply (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
      (f := fun s : ℝ => s ^ 2) (f' := fun s => 2 * s) (g := W)
      (continuous_id.pow 2).continuousOn
      (fun s _ => by simpa using hasDerivAt_pow 2 s) ?_).mpr
    · simpa only [Real.sq_sqrt p.tau_nonneg,
        Real.sq_sqrt (p.tau_nonneg.trans p.tau_lt.le)] using
        backwardPath_weightedKinetic_intervalIntegrable p hM12
    · intro s hs
      rw [min_eq_left hle, max_eq_right hle] at hs
      exact mul_nonneg (by norm_num) ((Real.sqrt_nonneg τ₁).trans hs.1.le)
  apply (htrans.const_mul 2).congr_uIoo
  intro s hs
  rw [uIoo_of_le hle] at hs
  have hsnonneg := (Real.sqrt_nonneg τ₁).trans hs.1.le
  simp only [W, Real.sqrt_sq hsnonneg, map_smul, smul_apply, smul_eq_mul]
  ring

end PoincareMT.M14
