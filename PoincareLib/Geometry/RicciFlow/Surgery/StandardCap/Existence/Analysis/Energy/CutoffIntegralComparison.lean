import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Support

/-!
# Compact-cutoff integral comparison

Local continuity on an open set containing the compact cutoff support
supplies genuine integrability. Pointwise finite-sum inequalities on that
support can then be integrated against a nonnegative cutoff. The domain
is an arbitrary topological measurable space with open sets measurable;
the measure need only be finite on compact sets. This is used in
Morgan-Tian Section 12.5, pp. 309-319 and canonical-local-integral-energy.md.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators

namespace MeasureTheory

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
  {U : Set X} {w f : X → ℝ}

/-- A continuous compact cutoff makes a locally continuous real field
integrable when its support lies in the true open domain
(Section 12.5, pp. 309-319). -/
theorem integrable_cutoff_mul (hU : IsOpen U) (hw : ContinuousOn w U)
    (hwc : HasCompactSupport w) (hwU : tsupport w ⊆ U) (hf : ContinuousOn f U) :
    Integrable (fun x => w x * f x) μ := by
  have hc : Continuous (fun x => w x * f x) :=
    (hw.mul hf).continuous_of_tsupport_subset hU
      (tsupport_mul_subset_left.trans hwU)
  exact hc.integrable_of_hasCompactSupport (hwc.mul_right (f' := f))

/-- A finite pointwise inequality on the cutoff support gives the same
integral inequality. No sign on the tested fields is required
(Section 12.5, pp. 309-319). -/
theorem integral_cutoff_mul_finsetSum_le {I : Type*} (s : Finset I)
    (hU : IsOpen U) (hw : ContinuousOn w U) (hwc : HasCompactSupport w)
    (hwU : tsupport w ⊆ U) (hw0 : ∀ x ∈ tsupport w, 0 ≤ w x)
    {q : I → X → ℝ} {g : X → ℝ}
    (hq : ∀ i ∈ s, ContinuousOn (q i) U) (hg : ContinuousOn g U)
    (hpoint : ∀ x ∈ tsupport w, (∑ i ∈ s, q i x) ≤ g x) :
    (∑ i ∈ s, ∫ x, w x * q i x ∂μ) ≤ ∫ x, w x * g x ∂μ := by
  have hqi (i : I) (hi : i ∈ s) : Integrable (fun x => w x * q i x) μ :=
    integrable_cutoff_mul hU hw hwc hwU (hq i hi)
  rw [← integral_finsetSum _ hqi]
  apply integral_mono (integrable_finsetSum _ hqi)
    (integrable_cutoff_mul hU hw hwc hwU hg)
  intro x
  by_cases hx : x ∈ tsupport w
  · simpa only [Finset.mul_sum] using
      mul_le_mul_of_nonneg_left (hpoint x hx) (hw0 x hx)
  · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul, Finset.sum_const_zero, le_refl]

end MeasureTheory
