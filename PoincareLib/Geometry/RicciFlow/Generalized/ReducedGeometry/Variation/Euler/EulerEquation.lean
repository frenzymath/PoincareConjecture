import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.SquareRoot.Action.SquareRootConstruction
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Pullback.PullbackRestriction
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Pullback.PullbackCongruence
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Euler.EulerContinuity
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.SquareRoot.Action.SquareRepresentative
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.Manifold.SectionThroughVector
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Theory

/-!
# Exact square-root regularization of every generalized Euler path

Morgan-Tian Definition 6.7 and Lemma 6.8, pp. 108-109. The actual
finite-energy construction supplies a smooth closed square-root path.
Extension independence transports the original Euler equation on the
interior; continuity against stationary smooth sections gives the
equation at both endpoints, without minimality or completeness.
-/

set_option autoImplicit false
-- The constructed square curve has the original squared base points definitionally.
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)

/-- The recovered square-root path satisfies the actual Euler equation
on its strict interior for every recovered velocity extension,
Definition 6.7 and Lemma 6.8, pp. 108-109. -/
theorem squareRootPathOfEuler_residual_interior
    (hCoordinates : M12MetricPredecessors.{0} n) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E₀ : M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity)
    (heuler : M14EulerEquation G p E₀)
    (E : M14PullbackExtension G (squareRootPathOfEuler p hCoordinates hM12 E₀ heuler).curve
      (M14SqrtParameterInterval τ₁ τ₂)
      (squareRootPathOfEuler p hCoordinates hM12 E₀ heuler).horizontal_velocity)
    {s : ℝ} (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
    (W : G.Horizontal (p.curve (s ^ 2))) :
    M14SquareRootEulerResidual G (squareRootPathOfEuler p hCoordinates hM12 E₀ heuler)
      E s W = 0 := by
  let R := squareRootPathOfEuler p hCoordinates hM12 E₀ heuler
  let J := Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)
  have hsub : J ⊆ M14SqrtParameterInterval τ₁ τ₂ := Ioo_subset_Icc_self
  have hY : ∀ r ∈ J, R.horizontal_velocity r = (2 * r) • p.horizontal_velocity (r ^ 2) := by
    intro r hr
    exact R.horizontal_agrees r hr
  let F := pullbackExtensionRestrict E hsub
  let ER : M14PullbackExtension G (fun r => p.curve (r ^ 2)) J
      (fun r => (2 * r) • p.horizontal_velocity (r ^ 2)) :=
    pullbackExtensionCongr F rfl (fun r hr => heq_of_eq (hY r hr))
  have hrestrict := horizontalCovariantDerivative_restrict E hsub (isOpen_Ioo.mem_nhds hs)
  have hcongr := horizontalCovariantDerivative_congr F rfl
    (fun r hr => heq_of_eq (hY r hr)) s
  have hregular : MDifferentiableWithinAt (𝓘(ℝ, ℝ)) (spacetimeModel n)
      (fun r => p.curve (r ^ 2)) J s :=
    ((R.smooth.mono hsub) s hs).mdifferentiableWithinAt (by simp)
  have hind := horizontalCovariantDerivative_extension_independent ER (squarePullbackExtension p E₀)
    hs (isOpen_Ioo.uniqueDiffOn s hs) hregular
  have hDX : M14HorizontalCovariantDerivative G R.curve
      (M14SqrtParameterInterval τ₁ τ₂) R.horizontal_velocity E s =
      M14HorizontalCovariantDerivative G (fun r => p.curve (r ^ 2)) J
        (fun r => (2 * r) • p.horizontal_velocity (r ^ 2)) (squarePullbackExtension p E₀) s :=
    hrestrict.trans ((eq_of_heq hcongr).trans hind)
  change G.spacetime.horizontalMetric.inner (p.curve (s ^ 2))
      (M14HorizontalCovariantDerivative G R.curve (M14SqrtParameterInterval τ₁ τ₂)
        R.horizontal_velocity E s) W -
    2 * s ^ 2 * M14HorizontalScalarDifferential G (p.curve (s ^ 2)) W.val +
    4 * s * horizontalRicci G.leafwise (p.curve (s ^ 2)) (R.horizontal_velocity s) W = 0
  rw [hDX, hY s hs, squarePullback_eulerResidual p hM12 E₀ hs W]
  have hτ : s ^ 2 ∈ Ioo τ₁ τ₂ := ⟨Real.lt_sq_of_sqrt_lt hs.1,
    (Real.lt_sqrt ((Real.sqrt_nonneg τ₁).trans_lt hs.1).le).mp hs.2⟩
  rw [heuler _ hτ W, mul_zero]

/-- The recovered square-root Euler equation holds at every closed
point, including initial time zero, Definition 6.7 and Lemma 6.8,
pp. 108-109. -/
theorem squareRootPathOfEuler_residual
    (hCoordinates : M12MetricPredecessors.{0} n) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E₀ : M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity)
    (heuler : M14EulerEquation G p E₀)
    (E : M14PullbackExtension G (squareRootPathOfEuler p hCoordinates hM12 E₀ heuler).curve
      (M14SqrtParameterInterval τ₁ τ₂)
      (squareRootPathOfEuler p hCoordinates hM12 E₀ heuler).horizontal_velocity)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂)
    (W : G.Horizontal (p.curve (s ^ 2))) :
    M14SquareRootEulerResidual G (squareRootPathOfEuler p hCoordinates hM12 E₀ heuler)
      E s W = 0 := by
  let R := squareRootPathOfEuler p hCoordinates hM12 E₀ heuler
  obtain ⟨Z, hZ, hZs⟩ := FiberBundle.exists_contMDiff_section_through
    (I := spacetimeModel n) (F := EuclideanSpace ℝ (Fin n)) W
  have hcont := squareRootEulerResidual_stationary_continuousOn (R := R) hM12 E Z hZ
  have hzero : EqOn (fun r => M14SquareRootEulerResidual G R E r (Z (R.curve r)))
      (fun _ => 0) (Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) := by
    intro r hr
    exact squareRootPathOfEuler_residual_interior p hCoordinates hM12 E₀ heuler E hr _
  have hclosed := hzero.of_subset_closure hcont continuousOn_const Ioo_subset_Icc_self
    (show M14SqrtParameterInterval τ₁ τ₂ ⊆ closure (Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) by
      rw [closure_Ioo (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt).ne]
      exact Subset.rfl)
  have hZs' : Z (R.curve s) = W := hZs
  simpa only [hZs'] using hclosed hs

/-- The exact frozen square-root regularization statement for every
supplied original Euler path, Definition 6.7 and Lemma 6.8, pp. 108-109. -/
theorem squareRootRegularizationStatement (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) : M14SquareRootRegularizationStatement G := by
  intro T τ₁ τ₂ x y p E₀ heuler
  let R := squareRootPathOfEuler p hCoordinates hM12 E₀ heuler
  obtain ⟨E⟩ := exists_squareRoot_velocity_extension R
  exact ⟨R, E, fun _ hs W => squareRootPathOfEuler_residual p hCoordinates hM12 E₀ heuler E hs W⟩

/-- Every supplied square-root representative of an original Euler path
satisfies the actual closed Euler equation, Lemma 6.8, pp. 108-109. -/
theorem squareRootEulerResidual_eq_zero_of_euler
    (hCoordinates : M12MetricPredecessors.{0} n) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E₀ : M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity)
    (heuler : M14EulerEquation G p E₀) (R : M14SquareRootPath G p)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂)
      R.horizontal_velocity) {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂)
    (W : G.Horizontal (R.curve s)) : M14SquareRootEulerResidual G R E s W = 0 := by
  let S := squareRootPathOfEuler p hCoordinates hM12 E₀ heuler
  obtain ⟨F⟩ := exists_squareRoot_velocity_extension S
  obtain ⟨W', hW⟩ : ∃ W' : G.Horizontal (S.curve s), HEq W W' := by
    rw [← squareRoot_curve_eqOn R S hs]
    exact ⟨W, HEq.rfl⟩
  exact (squareRootEulerResidual_congr R S E F hs hW).trans
    (squareRootPathOfEuler_residual p hCoordinates hM12 E₀ heuler F hs W')

end PoincareMT.M14
