import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.SquareRoot.Action.SquareCurve
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.SquareRoot.Action.SquareRootConstruction

/-!
# Actual backward paths from smooth square curves

Morgan-Tian Definition 6.7 and Lemma 6.8, pp. 108-109. A smooth
square curve with the exact backward clock gives an actual original
path and a square-root representative. Action integrability at zero
comes from the proved square substitution, without an Euler assumption.
-/

set_option autoImplicit false
-- The original and square curve records retain their actual tangent models.
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

/-- A smooth square curve with its exact clock gives the frozen
backward path between its actual endpoints. Integrability includes
initial time zero, Definition 6.7 and Lemma 6.8, pp. 108-109. -/
noncomputable def backwardPathOfSquareCurve
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) {T a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (α : ℝ → G.Point)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ α (M14SqrtParameterInterval a b))
    (hclock : ∀ s ∈ M14SqrtParameterInterval a b,
      G.spacetime.timeFunction (α s) = T - s ^ 2) :
    M14BackwardPath G T a b (α (Real.sqrt a)) (α (Real.sqrt b)) := by
  let γ := fun τ => α (Real.sqrt τ)
  have hγ := sqrtPullback_contMDiffOn ha hα
  have hγclock (τ : ℝ) (hτ : τ ∈ Icc a b) : G.spacetime.timeFunction (γ τ) = T - τ := by
    dsimp only [γ]
    rw [hclock _ ⟨Real.sqrt_le_sqrt hτ.1, Real.sqrt_le_sqrt hτ.2⟩,
      Real.sq_sqrt (ha.trans hτ.1)]
  refine {
    tau_nonneg := ha
    tau_lt := hab
    base_time := hγclock a ⟨le_rfl, hab.le⟩
    endpoint_time := hγclock b ⟨hab.le, le_rfl⟩
    curve := γ
    curve_start := rfl
    curve_end := rfl
    curve_time := hγclock
    curve_continuous := hα.continuousOn.comp Real.continuous_sqrt.continuousOn
      (fun τ hτ => ⟨Real.sqrt_le_sqrt hτ.1, Real.sqrt_le_sqrt hτ.2⟩)
    curve_regular := hγ.of_le (by simp)
    horizontal_velocity := projectedCurveVelocity G γ
    derivative_eq := ?_
    action_integrable := sqrtPullback_action_integrable hM12 ha hab hα }
  intro τ hτ
  apply projectedCurveVelocity_derivative_eq (T := T)
    (((hγ τ hτ).contMDiffAt (isOpen_Ioo.mem_nhds hτ)).mdifferentiableAt (by simp))
  filter_upwards [isOpen_Ioo.mem_nhds hτ] with t ht
  exact hγclock t (Ioo_subset_Icc_self ht)

/-- Smoothness of a path's actual square curve suffices to construct
its square-root record, with no Euler hypothesis. This is the
packaging step of Definition 6.7 and Lemma 6.8, pp. 108-109. -/
noncomputable def squareRootPathOfSmoothSquare
    {T a b : ℝ} {x y : G.Point} (p : M14BackwardPath G T a b x y)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ (fun s => p.curve (s ^ 2))
      (M14SqrtParameterInterval a b)) : M14SquareRootPath G p where
  curve s := p.curve (s ^ 2)
  domain := M14SqrtParameterInterval a b
  interval_subset := Subset.rfl
  smooth := hγ
  agrees _ _ := rfl
  curve_time s hs := p.curve_time _ (squarePath_parameter_mem p hs)
  horizontal_velocity := projectedCurveVelocityWithin G (fun s => p.curve (s ^ 2))
    (M14SqrtParameterInterval a b)
  horizontal_agrees s hs := by
    change projectedCurveVelocityWithin G (fun r => p.curve (r ^ 2))
      (M14SqrtParameterInterval a b) s = (2 * s) • p.horizontal_velocity (s ^ 2)
    unfold projectedCurveVelocityWithin
    rw [mfderivWithin_of_mem_nhds (I := 𝓘(ℝ, ℝ)) (I' := spacetimeModel n)
      (show M14SqrtParameterInterval a b ∈ 𝓝 s from Icc_mem_nhds hs.1 hs.2)]
    exact squarePath_projectedVelocity p hs
  derivative_eq s hs := squarePath_within_velocity_decomposition p hγ hs

variable (hM12 : GeneralizedRicciGaugeTheory.{u} n) {T a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
  (α : ℝ → G.Point)
  (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ α (M14SqrtParameterInterval a b))
  (hclock : ∀ s ∈ M14SqrtParameterInterval a b,
    G.spacetime.timeFunction (α s) = T - s ^ 2)

/-- The actual square-root representative of the path constructed
from a smooth square curve, Definition 6.7 and Lemma 6.8, pp. 108-109. -/
noncomputable def squareRootPathOfSquareCurve :
    M14SquareRootPath G (backwardPathOfSquareCurve hM12 ha hab α hα hclock) :=
  squareRootPathOfSmoothSquare _ (hα.congr (fun s hs => by
    change α (Real.sqrt (s ^ 2)) = α s
    rw [Real.sqrt_sq ((Real.sqrt_nonneg a).trans hs.1)]))

/-- The constructed square-root representative is the prescribed
square curve at every closed parameter point, including zero,
Definition 6.7 and Lemma 6.8, pp. 108-109. -/
theorem squareRootPathOfSquareCurve_curve {s : ℝ} (hs : s ∈ M14SqrtParameterInterval a b) :
    (squareRootPathOfSquareCurve hM12 ha hab α hα hclock).curve s = α s := by
  change α (Real.sqrt (s ^ 2)) = α s
  rw [Real.sqrt_sq ((Real.sqrt_nonneg a).trans hs.1)]

end PoincareMT.M14
