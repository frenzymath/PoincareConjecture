import Mathlib.Analysis.Calculus.MeanValue







set_option autoImplicit false

open Set Filter
open scoped Topology
namespace Poincare.Analysis


theorem sub_le_mul_sub_of_hasDerivAt_upper_support
    {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hsupport : ∀ x ∈ Ico a b, ∃ (g : ℝ → ℝ) (d : ℝ),
      HasDerivAt g d x ∧ g x = f x ∧ (∀ᶠ y in 𝓝 x, f y ≤ g y) ∧ d ≤ C) :
    f b - f a ≤ C * (b - a) := by
  have hb : f b ≤ f a + C * (b - a) := by
    apply image_le_of_liminf_slope_right_le_deriv_boundary hf
      (B := fun x => f a + C * (x - a)) (B' := fun _ => C)
      (by simp) (by fun_prop) ?_ ?_ ⟨hab, le_rfl⟩
    · intro x _
      simpa only [mul_one, id_eq] using ((((hasDerivAt_id x).sub_const a).const_mul C).const_add (f a)).hasDerivWithinAt
    · intro x hx r hr
      obtain ⟨g, d, hg, heq, hmajor, hd⟩ := hsupport x hx
      have hslopes : ∀ᶠ y in 𝓝[>] x, slope f x y ≤ slope g x y := by
        filter_upwards [hmajor.filter_mono nhdsWithin_le_nhds,
          self_mem_nhdsWithin] with y hy hxy
        simp only [slope_def_field, heq]
        exact div_le_div_of_nonneg_right (sub_le_sub_right hy _) (sub_nonneg.mpr (le_of_lt hxy))
      exact ((hg.hasDerivWithinAt.liminf_right_slope_le (hd.trans_lt hr)).and_eventually
        hslopes).mono (fun y hy => hy.2.trans_lt hy.1)
  linarith


theorem increment_le_of_fderiv_upper_support
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} (hs : Convex ℝ s) {f : E → ℝ} (hf : ContinuousOn f s)
    {v : E} {C : ℝ}
    (hsupport : ∀ x ∈ s, ∃ g : E → ℝ, DifferentiableAt ℝ g x ∧
      g x = f x ∧ (∀ᶠ y in 𝓝 x, f y ≤ g y) ∧ fderiv ℝ g x v ≤ C)
    {y : E} (hy : y ∈ s) {t : ℝ} (ht : 0 ≤ t) (hz : y + t • v ∈ s) :
    f (y + t • v) - f y ≤ t * C := by
  rcases ht.eq_or_lt with ht | ht
  · subst t
    simp
  have hmem : ∀ q ∈ Icc (0 : ℝ) t, y + q • v ∈ s := by
    intro q hq
    have hm := hs.add_smul_sub_mem hy hz
      (show q / t ∈ Icc (0 : ℝ) 1 from
        ⟨div_nonneg hq.1 ht.le, (div_le_one ht).mpr hq.2⟩)
    simpa only [add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ ht.ne'] using hm
  have hb := sub_le_mul_sub_of_hasDerivAt_upper_support ht.le
    (hf.comp (by fun_prop : ContinuousOn (fun q : ℝ => y + q • v) (Icc 0 t)) hmem)
    (C := C) (fun q hq => ?_)
  · simpa only [Function.comp_apply, zero_smul, add_zero, sub_zero, mul_comm] using hb
  obtain ⟨g, hg, heq, hmajor, hbound⟩ := hsupport (y + q • v) (hmem q ⟨hq.1, hq.2.le⟩)
  refine ⟨fun q : ℝ => g (y + q • v), fderiv ℝ g (y + q • v) v, ?_, heq, ?_, hbound⟩
  · have hline : HasDerivAt (fun q : ℝ => y + q • v) v q := by
      simpa only [id_eq, one_smul] using ((hasDerivAt_id q).smul_const v).const_add y
    exact hg.hasFDerivAt.comp_hasDerivAt q hline
  · exact (show ContinuousAt (fun q : ℝ => y + q • v) q by fun_prop).tendsto.eventually hmajor


theorem increment_bounds_of_fderiv_upper_support
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} (hs : Convex ℝ s) {f : E → ℝ} (hf : ContinuousOn f s)
    {v : E} {lo hi : ℝ}
    (hsupport : ∀ x ∈ s, ∃ g : E → ℝ, DifferentiableAt ℝ g x ∧
      g x = f x ∧ (∀ᶠ y in 𝓝 x, f y ≤ g y) ∧
        lo ≤ fderiv ℝ g x v ∧ fderiv ℝ g x v ≤ hi)
    {y : E} (hy : y ∈ s) {t : ℝ} (ht : 0 ≤ t) (hz : y + t • v ∈ s) :
    t * lo ≤ f (y + t • v) - f y ∧ f (y + t • v) - f y ≤ t * hi := by
  refine ⟨?_, increment_le_of_fderiv_upper_support hs hf
    (fun x hx => by
      obtain ⟨g, hg, heq, hmajor, _, hb⟩ := hsupport x hx
      exact ⟨g, hg, heq, hmajor, hb⟩) hy ht hz⟩
  have hback : (y + t • v) + t • (-v) = y := by simp
  have hrev := increment_le_of_fderiv_upper_support hs hf (v := -v) (C := -lo)
    (fun x hx => by
      obtain ⟨g, hg, heq, hmajor, hb, _⟩ := hsupport x hx
      refine ⟨g, hg, heq, hmajor, ?_⟩
      simpa only [map_neg, neg_le_neg_iff] using hb) hz ht (by simpa only [hback] using hy)
  rw [hback] at hrev
  linarith

end Poincare.Analysis
