import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Sard.Induction
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Sard.ChartReduction








open MeasureTheory Set Function
open scoped ContDiff Manifold Topology

namespace Poincare.Manifold

open Poincare.Analysis


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
