import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Covering.Basic

/-!
# Actual critical values of the equal-dimensional zero-chart projections

The exceptional set is the literal image of the points where the actual
derivative determinant vanishes. Mathlib's fixed-dimension Sard theorem
proves this set null. At every other value, the genuine inverse function
theorem isolates the fiber; compact portions are consequently finite.
MT Lemma 19.4, pp. 439-441; M65 derivation 49, sections 4-5.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory MeasureTheory.Measure
open scoped Topology ContDiff

namespace PoincareMT.M65Perturbation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A nonzero actual derivative determinant supplies a genuine local
inverse chart. MT Lemma 19.4, pp. 439-441; derivation 49, section 5. -/
theorem exists_local_inverse_of_det_ne_zero (f : E → E) (x : E)
    (hf : ContDiffAt ℝ 1 f x) (hdet : (fderiv ℝ f x).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph E E, x ∈ e.source ∧ (e : E → E) = f := by
  have hker : (fderiv ℝ f x).ker = ⊥ := by
    by_contra h
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
  have hrange : (fderiv ℝ f x).range = ⊤ :=
    LinearMap.ker_eq_bot_iff_range_eq_top.mp hker
  let A : E ≃L[ℝ] E := ContinuousLinearEquiv.ofBijective (fderiv ℝ f x) hker hrange
  have hA : HasFDerivAt f (A : E →L[ℝ] E) x := by
    rw [show (A : E →L[ℝ] E) = fderiv ℝ f x from
      ContinuousLinearEquiv.coe_ofBijective _ _ _]
    exact (hf.differentiableAt one_ne_zero).hasFDerivAt
  exact ⟨hf.toOpenPartialHomeomorph f hA one_ne_zero,
    hf.mem_toOpenPartialHomeomorph_source hA one_ne_zero, rfl⟩

variable [MeasurableSpace E] [BorelSpace E]

/-- The actual critical-value image of a C1 map on an open set is null,
and every other actual fiber is discrete. No generic value is supplied
as a hypothesis. MT Lemma 19.4, pp. 439-441; derivation 49, section 5. -/
theorem critical_image_null_and_fibers_discrete (mu : Measure E) [IsAddHaarMeasure mu]
    (f : E → E) (U : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) :
    mu (f '' {x ∈ U | (fderiv ℝ f x).det = 0}) = 0 ∧
      ∀ y ∉ f '' {x ∈ U | (fderiv ℝ f x).det = 0},
        IsDiscrete {x ∈ U | f x = y} := by
  constructor
  · apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero mu
      (f' := fun x => fderiv ℝ f x)
    · intro x hx
      have hD := ((hf.contDiffAt (hU.mem_nhds hx.1)).differentiableAt one_ne_zero).hasFDerivAt
      exact hD.hasFDerivWithinAt
    · intro x hx
      exact hx.2
  · intro y hy
    apply IsDiscrete.of_openPartialHomeomorph f (fun _ hx => hx.2)
    intro x hx
    apply exists_local_inverse_of_det_ne_zero f x (hf.contDiffAt (hU.mem_nhds hx.1))
    intro hdet
    exact hy ⟨x, ⟨hx.1, hdet⟩, hx.2⟩

/-- Removing the actual critical-value image makes every compact
portion of a C1 fiber finite. This is the finite-fiber consequence used
for the constructed zero-chart projections. MT Lemma 19.4, pp. 439-441;
derivation 49, section 5. -/
theorem compact_fiber_finite_of_not_critical (mu : Measure E) [IsAddHaarMeasure mu]
    (f : E → E) (U K : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hK : IsCompact K) (hKU : K ⊆ U) (y : E)
    (hy : y ∉ f '' {x ∈ U | (fderiv ℝ f x).det = 0}) :
    {x ∈ K | f x = y}.Finite := by
  have hclosed : IsClosed {x ∈ K | f x = y} :=
    hK.isClosed.isClosed_eq (hf.continuousOn.mono hKU) continuousOn_const
  apply (hK.of_isClosed_subset hclosed (fun _ hx => hx.1)).finite
  exact ((critical_image_null_and_fibers_discrete mu f U hU hf).2 y hy).mono
    (fun _ hx => ⟨hKU hx.1, hx.2⟩)

end PoincareMT.M65Perturbation
