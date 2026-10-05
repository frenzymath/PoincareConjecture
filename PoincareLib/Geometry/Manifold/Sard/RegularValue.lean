import PoincareLib.Analysis.Calculus.Sard.Basic
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Scalar regular values on smooth manifolds

A null set of critical values has dense complement. These lemmas select
regular values from that complement; scalar Sard supplies nullity separately.
-/

open MeasureTheory Set Function
open scoped ContDiff Manifold Topology

noncomputable section

namespace Poincare.Manifold

open Poincare.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [SecondCountableTopology M]

/-- A null critical-value image gives a dense set of regular scalar values on
the smooth manifold. -/
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

/-- Every nonempty open interval contains a regular value once the scalar
critical-value image is null. -/
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

/-- The positive cutoff interval used by the compact regular-domain consumer
has a regular scalar level under the same nullity hypothesis. -/
theorem exists_regular_value_unit_interval_of_manifold_critical_image_null
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hcrit : volume (f '' {x | ¬ Function.Surjective
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x)}) = 0) :
    ∃ c ∈ Set.Ioo (0 : ℝ) 1, ∀ x, f x = c → Function.Surjective
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x) := by
  exact exists_regular_value_in_interval_of_manifold_critical_image_null hf hcrit
    isOpen_Ioo ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩

end Poincare.Manifold

