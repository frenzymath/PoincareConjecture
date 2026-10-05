import PoincareLib.Geometry.Riemannian.Coordinates.Coefficients
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.SphereArea
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# The local alpha-one smoothness interface

This is one proposition with the actual planar weak first-variation
shape of Sacks--Uhlenbeck, Theorem 2.1, at alpha=1. It asserts no
supplier. The original continuous map and its true weak columns are
retained. M65 derivation 48 records the source-only future M60 edge;
no M60 proof module is imported.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff

noncomputable section

universe u

namespace PoincareMT

/-- The swappable local alpha=1 service for the same continuous weak
map, with its genuine metric variation and every integral meaningful.
There is no existence or regularity assertion in this definition.
Sacks--Uhlenbeck Theorem 2.1, pp. 6-8; M65 derivation 48. -/
def M65AlphaOneSmoothness {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) : Prop :=
  ∀ (b : M) (u : LoopPlane → EuclideanSpace ℝ (Fin n))
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)) (center : LoopPlane) (radius : ℝ),
    0 < radius →
    MapsTo u (Metric.closedBall center radius) (extChartAt (𝓡 n) b).target →
    ContinuousOn u (Metric.closedBall center radius) →
    MemLp u 2 (volume.restrict (Metric.ball center radius)) →
    (∀ i, MemLp (V i) 2 (volume.restrict (Metric.ball center radius))) →
    (∀ (i : Fin 2) (a : Fin n) (φ : LoopPlane → ℝ),
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Metric.ball center radius →
      IntegrableOn (fun z => u z a * fderiv ℝ φ z (EuclideanSpace.single i 1))
        (Metric.ball center radius) ∧
      IntegrableOn (fun z => V i z a * φ z) (Metric.ball center radius) ∧
      (∫ z in Metric.ball center radius,
        u z a * fderiv ℝ φ z (EuclideanSpace.single i 1)) =
        -(∫ z in Metric.ball center radius, V i z a * φ z)) →
    (let G := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
     ∀ φ : LoopPlane → EuclideanSpace ℝ (Fin n),
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Metric.ball center radius →
      let density := fun z =>
        (∑ i : Fin 2, fderiv ℝ G (u z) (φ z) (V i z) (V i z)) +
          2 * ∑ i : Fin 2, G (u z) (V i z)
            (fderiv ℝ φ z (EuclideanSpace.single i 1))
      IntegrableOn density (Metric.ball center radius) ∧
        (∫ z in Metric.ball center radius, density z) = 0) →
    ContDiffAt ℝ ∞ u center

end PoincareMT
