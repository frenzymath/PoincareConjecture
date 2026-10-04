import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Parameter integrals on a restricted parameter domain

A domain-restricted version of Mathlib's continuity theorem for a
parametric interval integral. It supplies endpoint continuity in the
2015 Morgan--Tian correction, Lemma 0.4, pp. 7-8.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped intervalIntegral

/-- Continuity of an integrand on the full integration axis times a parameter
set gives continuity of its fixed interval integral on that set.
Used for corrected Lemma 0.4, pp. 7-8, without extending endpoint data. -/
theorem ContinuousOn.intervalIntegral_prod_left
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure ℝ} [NullSingletonClass μ] [IsLocallyFiniteMeasure μ]
    {s : Set X} {f : ℝ × X → E} (hf : ContinuousOn f (univ ×ˢ s)) (l r : ℝ) :
    ContinuousOn (fun t ↦ ∫ x in l..r, f (x, t) ∂μ) s := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (t : s) x ↦ f (x, t))
    (hf.comp_continuous
      (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
      (fun z ↦ ⟨mem_univ _, z.1.property⟩)) l r
