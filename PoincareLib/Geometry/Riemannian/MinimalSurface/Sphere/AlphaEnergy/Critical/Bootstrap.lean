import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.AlphaEnergy.Critical.Interface
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Minimizer.Weak.Averages

/-!
# Local weak alpha Holder regularity

Sacks-Uhlenbeck Proposition 2.3, printed p. 7. This file retains the
actual C1 quarter-Holder output record and its weak averaging foundation.
The supplier is proved in `AlphaCriticalHolder.lean`, with the original
continuous coordinate map and columns, including alpha=1. Higher regularity belongs to
`AlphaCriticalProlongation.lean`; no smoothness of coefficients after
composition with the weak jet is assumed here.

The sphere-chart application uses exactly `S.coordinateData`. The single
threshold is chosen before the coordinate map and before all subsequent
jet orders. The record is kept below the affine jet helpers to avoid an
import cycle. The p=2 jet gain and higher-jet induction are separate.
-/

set_option autoImplicit false

open Set MeasureTheory ContinuousLinearMap
open scoped ContDiff Manifold Topology Convolution ENNReal

noncomputable section

universe u

namespace PoincareMT.M60

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Actual local C1 regularity of the same continuous weak map, with a
quarter-Holder bound for its classical derivative. The supplied weak
columns are retained by almost-everywhere equality. Source: SU 2.3,
the Holder step preceding the higher-jet argument. -/
structure SUC1HolderGain {m : ℕ}
    (u : LoopPlane → EuclideanSpace ℝ (Fin m))
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m))
    (center : LoopPlane) (outerRadius : ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt : radius < outerRadius
  coordinate_contDiff : ContDiffOn ℝ 1 u (Metric.ball center radius)
  column_ae : ∀ i : Fin 2, ∀ᵐ z ∂volume.restrict (Metric.ball center radius),
    fderiv ℝ u z (EuclideanSpace.single i 1) = V i z
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  derivative_holder : ∀ x ∈ Metric.closedBall center (radius / 2),
    ∀ y ∈ Metric.closedBall center (radius / 2),
    dist (fderiv ℝ u x) (fderiv ℝ u y) ≤
      constant * Real.sqrt (Real.sqrt (dist x y))

/-- The original weak alpha columns are precisely the derivatives of
every supported inner smooth average. This includes alpha=1 and uses
neither initial Hessian gain nor a global sphere. Source: SU Proposition
2.3, the first actual regularization step. -/
theorem SUWeakAlphaCoordinate.kernel_derivative
    {g : RiemannianMetric n M} {b : M} {alpha : ℝ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)}
    {center : LoopPlane} {radius : ℝ}
    (S : SUWeakAlphaCoordinate g b alpha u V center radius) (ha : 1 ≤ alpha)
    {φ : LoopPlane → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (x : LoopPlane) (hs : tsupport (fun y => φ (x - y)) ⊆ Metric.ball center radius)
    (i : Fin 2) :
    fderiv ℝ (φ ⋆[lsmul ℝ ℝ, volume] (Metric.ball center radius).indicator u) x
        (EuclideanSpace.single i 1) =
      (φ ⋆[lsmul ℝ ℝ, volume] (Metric.ball center radius).indicator (V i)) x := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball center radius)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top : volume (Metric.ball center radius) < ⊤)⟩
  have hq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * alpha) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hu : Integrable ((Metric.ball center radius).indicator u) volume :=
    (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mpr
      (S.coordinate_memLp.integrable hq)
  have hV : Integrable ((Metric.ball center radius).indicator (V i)) volume :=
    (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mpr
      ((S.column_memLp i).integrable hq)
  exact suWeak_convolution_fderiv Metric.isOpen_ball.measurableSet
    (S.weak_derivative i) hu.locallyIntegrable hV.locallyIntegrable hφ hc x hs

end PoincareMT.M60

end
