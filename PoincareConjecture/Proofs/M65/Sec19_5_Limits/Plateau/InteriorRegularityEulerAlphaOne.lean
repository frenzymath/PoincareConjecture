import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients
import PoincareConjecture.Definitions.M60Area
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture

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

end PoincareConjecture
