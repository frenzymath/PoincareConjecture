import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic










noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped intervalIntegral

namespace PoincareConjecture




theorem m64_setIntegral_inter_Icc_lower_bound
    {mu : Measure ℝ} [NullSingletonClass mu] {f : ℝ → ℝ}
    {a p q b : ℝ} (hap : a ≤ p) (hpq : p ≤ q) (hqb : q ≤ b)
    (hf : IntegrableOn f (Icc a b) mu)
    (hpos : ∀ x ∈ Icc a b, 0 ≤ f x)
    {S : Set ℝ} (hSsub : S ⊆ Icc a b) :
    (∫ x in S, f x ∂mu) - (∫ x in a..p, f x ∂mu) -
        (∫ x in q..b, f x ∂mu) ≤ ∫ x in S ∩ Icc p q, f x ∂mu := by
  have hab := hap.trans (hpq.trans hqb)
  have hcenter : Icc p q ⊆ Icc a b := Icc_subset_Icc hap hqb
  have hleft : IntervalIntegrable f mu a p :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hap).mpr
      (hf.mono_set (Icc_subset_Icc le_rfl (hpq.trans hqb)))
  have hmiddle : IntervalIntegrable f mu p q :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hpq).mpr (hf.mono_set hcenter)
  have hright : IntervalIntegrable f mu q b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hqb).mpr
      (hf.mono_set (Icc_subset_Icc (hap.trans hpq) le_rfl))
  have haddLeft := intervalIntegral.integral_add_adjacent_intervals hleft hmiddle
  have haddRight := intervalIntegral.integral_add_adjacent_intervals
    (hleft.trans hmiddle) hright
  have hIcc (s t : ℝ) (hst : s ≤ t) :
      (∫ x in Icc s t, f x ∂mu) = ∫ x in s..t, f x ∂mu := by
    rw [intervalIntegral.integral_of_le hst, integral_Icc_eq_integral_Ioc]
  have hremaining := setIntegral_sdiff (μ := mu) measurableSet_Icc hf hcenter
  rw [hIcc a b hab, hIcc p q hpq] at hremaining
  have hremove : (∫ x in S \ Icc p q, f x ∂mu) ≤
      ∫ x in Icc a b \ Icc p q, f x ∂mu := by
    apply setIntegral_mono_set (hf.mono_set sdiff_subset)
    · filter_upwards [ae_restrict_mem (measurableSet_Icc.diff measurableSet_Icc)] with x hx
      exact hpos x hx.1
    · exact Eventually.of_forall (fun x hx => ⟨hSsub hx.1, hx.2⟩)
  have hsplit := integral_inter_add_sdiff (μ := mu) (s := S) (t := Icc p q)
    measurableSet_Icc (hf.mono_set hSsub)
  linarith

end PoincareConjecture
