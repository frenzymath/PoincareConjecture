import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

open MeasureTheory Set
open scoped intervalIntegral

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
