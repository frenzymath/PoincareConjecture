import PoincareLib.Analysis.Calculus.Sard.Induction
import PoincareLib.Geometry.Manifold.Sard.ChartReduction

/-!
# Scalar Sard theorem

A smooth real-valued function on a finite-dimensional second-countable smooth
manifold has a null set of critical values. This is the scalar specialization
of Lee, Theorem 6.10, printed pp. 129-131.
-/

open MeasureTheory Set Function
open scoped ContDiff Manifold Topology

namespace Poincare.Manifold

open Poincare.Analysis

/-- The critical values of a smooth scalar function on a manifold are null. -/
theorem scalarCriticalImage_null_manifold
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    volume (f '' {x | ¬ Function.Surjective
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x)}) = 0 := by
  apply manifold_criticalImage_null_of_euclidean ?_ hf
  intro V g hV hg
  apply measure_mono_null _ (scalarCriticalImage_null_on hV hg)
  rintro y ⟨x, ⟨hx, hcrit⟩, rfl⟩
  refine ⟨x, ⟨hx, ?_⟩, rfl⟩
  by_contra hn
  apply hcrit
  apply LinearMap.surjective (f := (fderiv ℝ g x).toLinearMap)
  intro hz
  apply hn
  ext v
  exact congrArg (fun L => L v) hz

/-- Every nonempty open interval contains a regular value of a smooth scalar
function on a finite-dimensional second-countable manifold. -/
theorem exists_regular_value_in_interval_of_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {I : Set ℝ} (hI : IsOpen I) (hIn : I.Nonempty) :
    ∃ c ∈ I, ∀ x, f x = c → Function.Surjective
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x) := by
  exact exists_regular_value_in_interval_of_manifold_critical_image_null hf
    (scalarCriticalImage_null_manifold hf) hI hIn

end Poincare.Manifold

