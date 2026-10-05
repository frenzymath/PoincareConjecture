import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.LGeometry
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.SquareRoot.Action.SquareEnergy
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Path.ActionBounds

/-!
# Action control of arbitrary small-time competitors

Morgan-Tian Corollary 6.79, pp. 144-145. The whole-slab curvature
bound controls the scalar potential even before a competing path has
been confined to a local gauge. Its actual action then bounds its
square-time kinetic energy, without assuming that it is minimizing.
-/

set_option autoImplicit false
-- Selected slice tangent fibers retain the prescribed metric operations.
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

/-- M08's tensor contraction bound applies to the actual selected
slice, supplying scalar control in Corollary 6.79, pp. 144-145. -/
theorem horizontalScalarCurvature_abs_le_tensorNorm (q : G.Point) :
    |horizontalScalarCurvature G.leafwise q| ≤
      (n : ℝ) ^ 2 * horizontalCurvatureNorm G.leafwise q := by
  let S := G.slices (G.spacetime.timeFunction q)
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) S.Point := S.chartedSpace
  exact M08.scalarCurvature_abs_le_tensorNorm
    (G.leafwise.sliceConnection (G.spacetime.timeFunction q)) (spacetimeSlicePoint G.slices q)

variable {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)

/-- The actual square-time kinetic density of any admissible path,
equation (6.2), p. 106, used for confinement in Corollary 6.79. -/
noncomputable def pathSquareKinetic (s : ℝ) : ℝ :=
  G.spacetime.horizontalMetric.inner (p.curve (s ^ 2))
    ((2 * s) • p.horizontal_velocity (s ^ 2)) ((2 * s) • p.horizontal_velocity (s ^ 2))

/-- The actual square-time scalar potential of an admissible path,
equation (6.2), p. 106, used for confinement in Corollary 6.79. -/
noncomputable def pathSquarePotential (s : ℝ) : ℝ :=
  2 * s ^ 2 * horizontalScalarCurvature G.leafwise (p.curve (s ^ 2))

/-- The actual action is the nonsingular potential plus half the
square kinetic energy, including paths without endpoint derivatives,
equation (6.2), p. 106. -/
theorem backwardPath_squareAction_eq :
    M14BackwardLAction G p = ∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
      pathSquarePotential p s + (1 / 2 : ℝ) * pathSquareKinetic p s := by
  rw [backwardLAction_eq_transformed p]
  apply intervalIntegral.integral_congr_Ioo_of_le (Real.sqrt_le_sqrt p.tau_lt.le)
  intro s hs
  have hsnonneg := (Real.sqrt_nonneg τ₁).trans hs.1.le
  simp only [pathSquarePotential, pathSquareKinetic, M14BackwardLIntegrand,
    M14RawLIntegrand, Real.sqrt_sq hsnonneg, map_smul, smul_apply, smul_eq_mul]
  ring

/-- A lower scalar bound controls the entire square kinetic energy
by the actual action, the confinement estimate in Corollary 6.79,
pp. 144-145. No minimality or endpoint velocity is assumed. -/
theorem squarePath_kinetic_energy_le_action
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) {C : ℝ} (hC : 0 ≤ C)
    (hscalar : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
      -C ≤ horizontalScalarCurvature G.leafwise (p.curve (s ^ 2))) :
    (∫ s in Real.sqrt τ₁..Real.sqrt τ₂, pathSquareKinetic p s) ≤
      2 * M14BackwardLAction G p +
        4 * τ₂ * C * (Real.sqrt τ₂ - Real.sqrt τ₁) := by
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  have hpot : ContinuousOn (pathSquarePotential p) (M14SqrtParameterInterval τ₁ τ₂) :=
    (continuousOn_const.mul (continuousOn_id.pow 2)).mul
      (H.scalar_smooth.continuous.comp_continuousOn (squarePath_continuousOn p))
  have hle := Real.sqrt_le_sqrt p.tau_lt.le
  have hp : IntervalIntegrable (pathSquarePotential p) MeasureTheory.volume
      (Real.sqrt τ₁) (Real.sqrt τ₂) := hpot.intervalIntegrable_of_Icc hle
  have hk : IntervalIntegrable (pathSquareKinetic p) MeasureTheory.volume
      (Real.sqrt τ₁) (Real.sqrt τ₂) := squarePath_kinetic_intervalIntegrable p hM12
  have hlower : ∀ s ∈ Icc (Real.sqrt τ₁) (Real.sqrt τ₂),
      -(2 * τ₂ * C) ≤ pathSquarePotential p s := by
    intro s hs
    have ht := (squarePath_parameter_mem p hs).2
    have hR := mul_le_mul_of_nonneg_left (hscalar s hs) (by positivity : 0 ≤ 2 * s ^ 2)
    have hc := mul_le_mul_of_nonneg_right ht hC
    dsimp only [pathSquarePotential]
    nlinarith
  have hi := intervalIntegral.integral_mono_on hle
    (intervalIntegrable_const (c := -(2 * τ₂ * C))) hp hlower
  rw [intervalIntegral.integral_const, smul_eq_mul] at hi
  have ha := backwardPath_squareAction_eq p
  rw [intervalIntegral.integral_add hp (hk.const_mul (1 / 2)),
    intervalIntegral.integral_const_mul] at ha
  linarith

/-- A whole-slab curvature bound supplies the preceding energy
estimate for every admissible competitor, Corollary 6.79,
pp. 144-145, including dimension zero. -/
theorem squarePath_kinetic_energy_le_of_curvature_bound
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) {δ C : ℝ}
    (hτ : τ₂ ≤ δ) (hC : 0 ≤ C)
    (hcurv : ∀ q : G.Point, G.spacetime.timeFunction q ∈ Icc (T - δ) T →
      horizontalCurvatureNorm G.leafwise q ≤ C) :
    (∫ s in Real.sqrt τ₁..Real.sqrt τ₂, pathSquareKinetic p s) ≤
      2 * M14BackwardLAction G p +
        4 * τ₂ * ((n : ℝ) ^ 2 * C) * (Real.sqrt τ₂ - Real.sqrt τ₁) := by
  apply squarePath_kinetic_energy_le_action p hM12 (mul_nonneg (sq_nonneg _) hC)
  intro s hs
  have ht := squarePath_parameter_mem p hs
  have htime : G.spacetime.timeFunction (p.curve (s ^ 2)) ∈ Icc (T - δ) T := by
    rw [p.curve_time _ ht]
    exact ⟨sub_le_sub_left (ht.2.trans hτ) T,
      sub_le_self _ (p.tau_nonneg.trans ht.1)⟩
  exact (abs_le.mp ((horizontalScalarCurvature_abs_le_tensorNorm (p.curve (s ^ 2))).trans
    (mul_le_mul_of_nonneg_left (hcurv _ htime) (sq_nonneg _)))).1

end PoincareMT.M14
