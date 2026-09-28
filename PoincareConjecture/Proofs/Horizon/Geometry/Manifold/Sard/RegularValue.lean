import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Sard.Basic
import Mathlib.Geometry.Manifold.Instances.Real

open MeasureTheory Set Function
open scoped ContDiff Manifold Topology

noncomputable section

namespace Poincare.Manifold

open Poincare.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [SecondCountableTopology M]

theorem dense_regular_values_of_manifold_critical_image_null
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hcrit : volume (f '' {x | ¬ Function.Surjective
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x)}) = 0) :
    Dense {c : ℝ | ∀ x, f x = c → Function.Surjective
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x)} := by
  let C : Set ℝ := f '' {x | ¬ Function.Surjective
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x)}
  have hC : Dense Cᶜ := dense_compl_of_measure_zero_image volume hcrit
  have hregular :
      {c : ℝ | ∀ x, f x = c → Function.Surjective
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x)} = Cᶜ := by
    ext c
    constructor
    · intro hc ⟨x, hx, hfx⟩
      exact hx (hc x hfx)
    · intro hc x hfx
      by_contra hns
      exact hc ⟨x, hns, hfx⟩
  rw [hregular]
  exact hC

theorem exists_regular_value_in_interval_of_manifold_critical_image_null
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hcrit : volume (f '' {x | ¬ Function.Surjective
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x)}) = 0)
    {I : Set ℝ} (hI : IsOpen I) (hIn : I.Nonempty) :
    ∃ c ∈ I, ∀ x, f x = c → Function.Surjective
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x) := by
  rcases (dense_iff_inter_open.mp
    (dense_regular_values_of_manifold_critical_image_null hf hcrit) I hI hIn) with
    ⟨c, hcI, hc⟩
  exact ⟨c, hcI, hc⟩

theorem exists_regular_value_unit_interval_of_manifold_critical_image_null
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hcrit : volume (f '' {x | ¬ Function.Surjective
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x)}) = 0) :
    ∃ c ∈ Set.Ioo (0 : ℝ) 1, ∀ x, f x = c → Function.Surjective
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x) := by
  exact exists_regular_value_in_interval_of_manifold_critical_image_null hf hcrit
    isOpen_Ioo ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩

end Poincare.Manifold
