import PoincareLib.Geometry.Riemannian.Measure.Density
import PoincareLib.Geometry.Riemannian.Measure.Basic
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Change of parameters for the local metric density

The Gram-determinant chain rule cancels the Euclidean Jacobian in the
change-of-variables formula. This establishes consistency of local density
integrals; it does not yet identify them with intrinsic Hausdorff volume.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Local metric-density integrals are invariant under injective differentiable
changes of parameters. -/
theorem lintegral_pullbackVolumeDensity_image (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M}
    {e : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, MDifferentiableAt (𝓡 n) (𝓡 n) f (e x))
    (he : ∀ x ∈ s, DifferentiableAt ℝ e x) (hinj : InjOn e s)
    (u : M → ℝ≥0∞) :
    ∫⁻ x in e '' s, ENNReal.ofReal (g.pullbackVolumeDensity f x) * u (f x) =
      ∫⁻ x in s, ENNReal.ofReal (g.pullbackVolumeDensity (f ∘ e) x) * u (f (e x)) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun x hx ↦ (he x hx).hasFDerivAt.hasFDerivWithinAt) hinj]
  apply setLIntegral_congr_fun hs
  intro x hx
  dsimp only
  erw [g.pullbackVolumeDensity_comp (hf x hx) (he x hx),
    ENNReal.ofReal_mul (abs_nonneg _), mul_assoc]

end PoincareMT.RiemannianMetric
