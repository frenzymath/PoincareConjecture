import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Coordinates.CoordinateVolumeBounds
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Basic.CenteredDiffeomorph

/-!
# Centering actual Euclidean source coordinates

Translation of the source has identity differential. It preserves the
pullback bilinear form and its Gram Jacobian at the translated point.
Source: Morgan-Tian Proposition 12.13, pp. 304-306.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M34

/-- Translating the source of the identity chart just evaluates the same
metric coefficients at the translated point (Proposition 12.13). -/
theorem modelTranslationDiffeomorph_pullbackMetricForm {n : ℕ}
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (x z : EuclideanSpace ℝ (Fin n)) :
    M10.pullbackMetricForm g (modelTranslationDiffeomorph (𝕜 := ℝ) x) z =
      M10.pullbackMetricForm g id (x + z) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  change g.inner (x + z)
    (mfderiv (𝓡 n) (𝓡 n) (modelTranslationDiffeomorph (𝕜 := ℝ) x) z v)
    (mfderiv (𝓡 n) (𝓡 n) (modelTranslationDiffeomorph (𝕜 := ℝ) x) z w) =
      g.inner (x + z) (mfderiv (𝓡 n) (𝓡 n) id (x + z) v)
        (mfderiv (𝓡 n) (𝓡 n) id (x + z) w)
  rw [modelTranslationDiffeomorph_mfderiv, mfderiv_id]
  rfl

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The full actual bilinear form is unchanged by recentering coordinates
(Proposition 12.13, pp. 304-306). -/
theorem centeredDiffeomorph_pullbackMetricForm (g : RiemannianMetric n M)
    (e : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    (x z : EuclideanSpace ℝ (Fin n)) (hxz : x + z ∈ e.source) :
    M10.pullbackMetricForm g (centeredDiffeomorph e x) z =
      M10.pullbackMetricForm g e (x + z) := by
  have hd := mfderiv_comp z (e.mdifferentiableAt (by simp) hxz)
    ((modelTranslationDiffeomorph (𝕜 := ℝ) x).contMDiffAt.mdifferentiableAt (by simp))
  change mfderiv (𝓡 n) (𝓡 n) (fun y => e (x + y)) z =
    (mfderiv (𝓡 n) (𝓡 n) e (x + z)).comp
      (mfderiv (𝓡 n) (𝓡 n) (modelTranslationDiffeomorph (𝕜 := ℝ) x) z) at hd
  rw [modelTranslationDiffeomorph_mfderiv] at hd
  have hderiv : mfderiv (𝓡 n) (𝓡 n) (centeredDiffeomorph e x) z =
      mfderiv (𝓡 n) (𝓡 n) e (x + z) := by
    convert! hd using 1
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  change g.inner (e (x + z))
    (mfderiv (𝓡 n) (𝓡 n) (centeredDiffeomorph e x) z v)
    (mfderiv (𝓡 n) (𝓡 n) (centeredDiffeomorph e x) z w) = _
  rw [hderiv]
  rfl

end PoincareMT.M34
