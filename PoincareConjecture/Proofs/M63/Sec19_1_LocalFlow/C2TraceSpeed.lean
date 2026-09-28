import PoincareConjecture.Proofs.M62.Lemma0_4_Continuity
import PoincareConjecture.Proofs.M62.Lemma0_2_NormalizedFields
import PoincareConjecture.Statements.Ch19.CurveEvolution
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus











set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle intervalIntegral Topology

universe u

namespace PoincareConjecture.M63

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)

private theorem normalizationCoefficient_abs_le (hc : M62ShrinkingCurve F c)
    {K0 K1 K2 R : ℝ} (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    (x : ℝ) {t : ℝ} (ht : t ∈ Ioo a b)
    (hR : m62CurvatureSquared F c t x ≤ R) :
    |m62TangentRicci F c t x + m62CurvatureSquared F c t x| ≤ K2 + R := by
  have hunit := (unitTangent_norm F c hc (Ioo_subset_Icc_self ht) x).le
  have hRic : |m62TangentRicci F c t x| ≤ K2 :=
    hBounds.ricci t (Ioo_subset_Icc_self ht) (c x t)
      (spatialUnitTangent F c t x) (spatialUnitTangent F c t x) hunit hunit
  calc
    _ ≤ |m62TangentRicci F c t x| + |m62CurvatureSquared F c t x| := abs_add_le _ _
    _ = |m62TangentRicci F c t x| + m62CurvatureSquared F c t x := by
      rw [abs_of_nonneg (curvatureSquared_nonneg F c t x)]
    _ ≤ K2 + R := add_le_add hRic hR





theorem normalizationCoefficient_intervalIntegrable (hc : M62ShrinkingCurve F c)
    {K0 K1 K2 R : ℝ} (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    (x : ℝ) (hR : ∀ r ∈ Ioo a b, m62CurvatureSquared F c r x ≤ R)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    IntervalIntegrable
      (fun r => m62TangentRicci F c r x + m62CurvatureSquared F c r x) volume s t := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hst]
  have hslice : Continuous (fun r : ℝ => (x, r)) := continuous_const.prodMk continuous_id
  have hglobal : ContinuousOn (fun z : ℝ × ℝ =>
      m62TangentRicci F c z.2 z.1 + m62CurvatureSquared F c z.2 z.1)
      (univ ×ˢ Ioo a b) := (normalization_coefficient_contDiffOn F c hc).continuousOn
  have hmaps : MapsTo (fun r : ℝ => (x, r)) (Ioo s t) (univ ×ˢ Ioo a b) := by
    intro r hr
    exact ⟨mem_univ _, hs.1.trans_lt hr.1, hr.2.trans_le ht.2⟩
  have hcont : ContinuousOn
      (fun r => m62TangentRicci F c r x + m62CurvatureSquared F c r x) (Ioo s t) := by
    simpa +instances only [Function.comp_def] using!
      hglobal.comp hslice.continuousOn hmaps
  apply (integrable_const (K2 + R)).mono' (hcont.aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with r hr
  rw [Real.norm_eq_abs]
  have hr' : r ∈ Ioo a b := ⟨hs.1.trans_lt hr.1, hr.2.trans_le ht.2⟩
  exact normalizationCoefficient_abs_le F c hc hBounds x hr' (hR r hr')





theorem curveSpeed_log_eq_integral (hc : M62ShrinkingCurve F c)
    {K0 K1 K2 R : ℝ} (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    (x : ℝ) (hR : ∀ r ∈ Ioo a b, m62CurvatureSquared F c r x ≤ R)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    Real.log (curveSpeed F c t x) = Real.log (curveSpeed F c s x) -
      ∫ r in s..t, m62TangentRicci F c r x + m62CurvatureSquared F c r x := by
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  have hcont : ContinuousOn (fun r => curveSpeed F c r x) (Icc s t) :=
    (speed_continuousOn F c hc).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (by intro r hr; exact ⟨mem_univ _, hsub hr⟩)
  have hlog := hcont.log (fun r hr => (speed_pos F c hc (hsub hr) x).ne')
  have hderiv (r : ℝ) (hr : r ∈ Ioo s t) :
      HasDerivAt (fun r => Real.log (curveSpeed F c r x))
        (-(m62TangentRicci F c r x + m62CurvatureSquared F c r x)) r := by
    have hr' : r ∈ Ioo a b := ⟨hs.1.trans_lt hr.1, hr.2.trans_le ht.2⟩
    have hv := (speed_pos F c hc (Ioo_subset_Icc_self hr') x).ne'
    convert! (hasDerivAt_speed F c hc hr' x).log hv using 1
    field_simp
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hlog hderiv
    (normalizationCoefficient_intervalIntegrable F c hc hBounds x hR hs ht hst).neg
  rw [intervalIntegral.integral_neg] at hFTC
  linarith





theorem curveSpeed_exp_bounds (hc : M62ShrinkingCurve F c)
    {K0 K1 K2 R : ℝ} (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    (x : ℝ) (hR : ∀ r ∈ Ioo a b, m62CurvatureSquared F c r x ≤ R)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    curveSpeed F c s x * Real.exp (-(K2 + R) * (t - s)) ≤ curveSpeed F c t x ∧
      curveSpeed F c t x ≤ curveSpeed F c s x * Real.exp ((K2 + R) * (t - s)) := by
  let I : ℝ := ∫ r in s..t,
    m62TangentRicci F c r x + m62CurvatureSquared F c r x
  have hI : |I| ≤ (K2 + R) * (t - s) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const_ae
      (a := s) (b := t) (C := K2 + R)
      (f := fun r => m62TangentRicci F c r x + m62CurvatureSquared F c r x) (by
        filter_upwards [volume.ae_ne t] with r hrt
        intro hr
        rw [uIoc_of_le hst] at hr
        have hr' : r ∈ Ioo a b :=
          ⟨hs.1.trans_lt hr.1, (lt_of_le_of_ne hr.2 hrt).trans_le ht.2⟩
        rw [Real.norm_eq_abs]
        exact normalizationCoefficient_abs_le F c hc hBounds x hr' (hR r hr'))
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hst), I] using h
  have heq : curveSpeed F c t x = curveSpeed F c s x * Real.exp (-I) := by
    calc
      _ = Real.exp (Real.log (curveSpeed F c t x)) :=
        (Real.exp_log (speed_pos F c hc ht x)).symm
      _ = Real.exp (Real.log (curveSpeed F c s x) - I) := by
        rw [curveSpeed_log_eq_integral F c hc hBounds x hR hs ht hst]
      _ = _ := by rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (speed_pos F c hc hs x)]
  rw [heq]
  constructor
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (by linarith [(abs_le.mp hI).2])) (speed_nonneg F c s x)
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (by linarith [(abs_le.mp hI).1])) (speed_nonneg F c s x)

end PoincareConjecture.M63
