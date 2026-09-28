import PoincareConjecture.Proofs.M65.Def18_23_Profile.ProfileODE
import PoincareConjecture.Proofs.M65.Def18_23_Profile.AreaComparisonProfile

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} (F : RicciFlow 3 M (Set.Icc a b))

noncomputable def m65RestartedAreaProfile (s A t : ℝ) : ℝ :=
  areaComparisonProfile F 0 t +
    Real.exp ((∫ r in a..s, flowScalarCurvatureInfimum F r / 2) -
      (∫ r in a..t, flowScalarCurvatureInfimum F r / 2)) *
        (A - areaComparisonProfile F 0 s)

@[simp] theorem m65RestartedAreaProfile_initial (s A : ℝ) :
    m65RestartedAreaProfile F s A s = A := by
  simp [m65RestartedAreaProfile]

theorem m65RestartedAreaProfile_difference (s A B t : ℝ) :
    m65RestartedAreaProfile F s A t - areaComparisonProfile F B t =
      Real.exp ((∫ r in a..s, flowScalarCurvatureInfimum F r / 2) -
        (∫ r in a..t, flowScalarCurvatureInfimum F r / 2)) *
          (A - areaComparisonProfile F B s) := by
  let P : ℝ → ℝ := fun t => ∫ r in a..t, flowScalarCurvatureInfimum F r / 2
  have hs := areaComparisonProfile_sub F B 0 s
  have ht := areaComparisonProfile_sub F B 0 t
  have hexp : Real.exp (P s - P t) * Real.exp (-P s) = Real.exp (-P t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold m65RestartedAreaProfile
  change areaComparisonProfile F 0 t + Real.exp (P s - P t) *
    (A - areaComparisonProfile F 0 s) - areaComparisonProfile F B t = _
  linear_combination Real.exp (P s - P t) * hs - ht + B * hexp

@[simp] theorem m65RestartedAreaProfile_at_start (A t : ℝ) :
    m65RestartedAreaProfile F a A t = areaComparisonProfile F A t := by
  have h := m65RestartedAreaProfile_difference F a A A t
  rw [areaComparisonProfile_initial, sub_self, mul_zero] at h
  exact sub_eq_zero.mp h

theorem areaComparisonPrimitive_hasDerivWithinAt
    (compact : IsCompact (Set.univ : Set M)) {t : ℝ} (ht : t ∈ Set.Icc a b) :
    HasDerivWithinAt (fun t => ∫ r in a..t, flowScalarCurvatureInfimum F r / 2)
      (flowScalarCurvatureInfimum F t / 2) (Set.Icc a b) t := by
  have hq := (flowScalarCurvatureInfimum_continuousOn F compact).div_const 2
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have : Fact (t ∈ Set.Icc a b) := ⟨ht⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right
    ((hq.mono (Set.uIcc_subset_Icc ha ht)).intervalIntegrable)
    (hq.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hq t ht)

theorem m65RestartedAreaProfile_hasDerivWithinAt
    (compact : IsCompact (Set.univ : Set M)) (s A : ℝ)
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    HasDerivWithinAt (m65RestartedAreaProfile F s A)
      (-2 * Real.pi - flowScalarCurvatureInfimum F t * m65RestartedAreaProfile F s A t / 2)
      (Set.Icc a b) t := by
  have hdP := areaComparisonPrimitive_hasDerivWithinAt F compact ht
  have hdw := areaComparisonProfile_hasDerivWithinAt F compact 0 ht
  have hd := hdw.add (((hdP.const_sub
    (∫ r in a..s, flowScalarCurvatureInfimum F r / 2)).exp).mul_const
      (A - areaComparisonProfile F 0 s))
  refine hd.congr_deriv ?_
  unfold m65RestartedAreaProfile
  ring

end PoincareConjecture
