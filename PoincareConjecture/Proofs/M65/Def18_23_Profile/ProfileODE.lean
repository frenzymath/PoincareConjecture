import PoincareConjecture.Proofs.M65.Def18_23_Profile.ScalarInfimum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

open MeasureTheory

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {t₀ t₁ : ℝ} (F : RicciFlow 3 M (Set.Icc t₀ t₁))

theorem areaComparisonPrimitive_continuousOn
    (compact : IsCompact (Set.univ : Set M)) :
    ContinuousOn (fun t => ∫ s in t₀..t, flowScalarCurvatureInfimum F s / 2)
      (Set.Icc t₀ t₁) := by
  have horder : t₀ ≤ t₁ := by
    obtain ⟨t, ht⟩ := F.nontrivial.nonempty
    exact ht.1.trans ht.2
  have hint := flowScalarCurvatureInfimum_intervalIntegrable F compact
    (show t₀ ∈ Set.Icc t₀ t₁ from ⟨le_rfl, horder⟩)
    (show t₁ ∈ Set.Icc t₀ t₁ from ⟨horder, le_rfl⟩)
  simpa only [Set.uIcc_of_le horder] using
    intervalIntegral.continuousOn_primitive_interval' hint Set.left_mem_uIcc

theorem areaComparisonProfile_continuousOn
    (compact : IsCompact (Set.univ : Set M)) (a : ℝ) :
    ContinuousOn (areaComparisonProfile F a) (Set.Icc t₀ t₁) := by
  have horder : t₀ ≤ t₁ := by
    obtain ⟨t, ht⟩ := F.nontrivial.nonempty
    exact ht.1.trans ht.2
  have hprim := areaComparisonPrimitive_continuousOn F compact
  have hint := hprim.rexp.intervalIntegrable_of_Icc (μ := volume) horder
  have hexpprim : ContinuousOn
      (fun t => ∫ s in t₀..t,
        Real.exp (∫ v in t₀..s, flowScalarCurvatureInfimum F v / 2))
      (Set.Icc t₀ t₁) := by
    simpa only [Set.uIcc_of_le horder] using
      intervalIntegral.continuousOn_primitive_interval' hint Set.left_mem_uIcc
  exact hprim.neg.rexp.mul
    (continuousOn_const.sub (continuousOn_const.mul hexpprim))

theorem areaComparisonProfile_hasDerivWithinAt
    (compact : IsCompact (Set.univ : Set M)) (a : ℝ)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    HasDerivWithinAt (areaComparisonProfile F a)
      (-2 * Real.pi - flowScalarCurvatureInfimum F t *
        areaComparisonProfile F a t / 2) (Set.Icc t₀ t₁) t := by
  let q : ℝ → ℝ := fun s => flowScalarCurvatureInfimum F s / 2
  let primitive : ℝ → ℝ := fun s => ∫ v in t₀..s, q v
  have hq : ContinuousOn q (Set.Icc t₀ t₁) :=
    (flowScalarCurvatureInfimum_continuousOn F compact).div_const 2
  have hprim : ContinuousOn primitive (Set.Icc t₀ t₁) :=
    areaComparisonPrimitive_continuousOn F compact
  have hstart : t₀ ∈ Set.Icc t₀ t₁ := ⟨le_rfl, ht.1.trans ht.2⟩
  have : Fact (t ∈ Set.Icc t₀ t₁) := ⟨ht⟩
  have hdprim : HasDerivWithinAt primitive (q t) (Set.Icc t₀ t₁) t :=
    intervalIntegral.integral_hasDerivWithinAt_right
      ((hq.mono (Set.uIcc_subset_Icc hstart ht)).intervalIntegrable)
      (hq.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hq t ht)
  have hdexpprim : HasDerivWithinAt
      (fun s => ∫ v in t₀..s, Real.exp (primitive v)) (Real.exp (primitive t))
      (Set.Icc t₀ t₁) t :=
    intervalIntegral.integral_hasDerivWithinAt_right
      ((hprim.rexp.mono (Set.uIcc_subset_Icc hstart ht)).intervalIntegrable)
      (hprim.rexp.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t)
      (hprim.rexp t ht)
  have hproduct := hdprim.neg.exp.mul ((hdexpprim.const_mul (2 * Real.pi)).const_sub a)
  have hexp : Real.exp (-primitive t) * Real.exp (primitive t) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  refine hproduct.congr_deriv ?_
  change _ = -2 * Real.pi - flowScalarCurvatureInfimum F t *
    (Real.exp (-primitive t) *
      (a - 2 * Real.pi * ∫ v in t₀..t, Real.exp (primitive v))) / 2
  dsimp only [q, Pi.neg_apply]
  linear_combination -2 * Real.pi * hexp

end PoincareConjecture
