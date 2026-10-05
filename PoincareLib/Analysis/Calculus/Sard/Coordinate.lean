import PoincareLib.Analysis.Calculus.Sard.Basic
import PoincareLib.Analysis.Calculus.Sard.LevelSet

/-!
# Checked branches for the scalar Sard reduction

The one-dimensional coordinate branch follows from the Jacobian image theorem.
The residual branch follows from a local Holder estimate and Hausdorff dimension
comparison. Regular hypersurface coordinates support the dimension induction.
-/

open MeasureTheory Set Function
open scoped ContDiff Topology

namespace Poincare.Analysis

/-- The scalar coordinate branch: critical values of a smooth real function
have zero Lebesgue measure. -/
theorem scalarCriticalImage_null_coordinate
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    volume (f '' {x | ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  apply critical_values_null_one_dim volume
  · intro x hx
    exact ((hf.differentiable (by simp)).differentiableAt).hasFDerivAt.hasFDerivWithinAt
  · intro x hx
    by_contra hdet
    have hnonzero : (fderiv ℝ f x).toLinearMap ≠ 0 := by
      intro hz
      apply hdet
      simp [ContinuousLinearMap.det, hz]
    exact hx (LinearMap.surjective hnonzero)

/-- The residual branch closes whenever the local Taylor remainder has exponent
strictly larger than the source-to-target dimension ratio. -/
theorem scalarCriticalImage_null_residual
    {m : ℕ} {s : Set (EuclideanSpace ℝ (Fin m))}
    {n : ℕ} {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    [MeasurableSpace (EuclideanSpace ℝ (Fin m))]
    [BorelSpace (EuclideanSpace ℝ (Fin m))]
    [MeasurableSpace (EuclideanSpace ℝ (Fin n))]
    [BorelSpace (EuclideanSpace ℝ (Fin n))]
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    {r : NNReal} (hr : 0 < r)
    (hholder :
      ∀ x ∈ s, ∃ C : NNReal, ∃ t ∈ nhdsWithin x s,
        HolderOnWith C r f t)
    (hdim :
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) : ENNReal) / r <
        Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :
    μ (f '' s) = 0 := by
  apply measure_zero_image_of_locallyHolderOnWith_of_finrank_div_lt
    (μ := μ) hr hholder hdim

/-- Three locally null branch images have a null union.  This is the set-theoretic
assembly consumed after the coordinate, hypersurface, and residual producers
have been established. -/
theorem scalarCriticalImage_null_of_three_branches
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {A B C : Set α}
    (hA : μ A = 0) (hB : μ B = 0) (hC : μ C = 0) :
    μ (A ∪ B ∪ C) = 0 := by
  exact measure_union_null (measure_union_null hA hB) hC

end Poincare.Analysis

