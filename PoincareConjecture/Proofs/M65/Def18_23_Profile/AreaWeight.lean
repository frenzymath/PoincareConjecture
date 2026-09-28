import PoincareConjecture.Proofs.M65.Def18_23_Profile.RestartedProfile








set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} (F : RicciFlow 3 M (Set.Icc a b))


noncomputable def m65AreaWeight (t : ℝ) : ℝ :=
  Real.exp (∫ r in a..t, flowScalarCurvatureInfimum F r / 2)



noncomputable def m65WeightedArea (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  m65AreaWeight F t * f t + 2 * Real.pi * ∫ r in a..t, m65AreaWeight F r


theorem m65AreaWeight_pos (t : ℝ) : 0 < m65AreaWeight F t := Real.exp_pos _



@[simp] theorem m65WeightedArea_initial (f : ℝ → ℝ) : m65WeightedArea F f a = f a := by
  simp [m65WeightedArea, m65AreaWeight]



theorem m65WeightedArea_profile_error (f : ℝ → ℝ) (A t : ℝ) :
    m65WeightedArea F f t - A =
      m65AreaWeight F t * (f t - areaComparisonProfile F A t) := by
  let P := ∫ r in a..t, flowScalarCurvatureInfimum F r / 2
  have hexp : Real.exp P * Real.exp (-P) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  change Real.exp P * f t + 2 * Real.pi * (∫ r in a..t, m65AreaWeight F r) - A =
    Real.exp P * (f t - Real.exp (-P) * (A - 2 * Real.pi * ∫ r in a..t, m65AreaWeight F r))
  linear_combination
    (A - 2 * Real.pi * ∫ r in a..t, m65AreaWeight F r) * hexp



theorem m65AreaWeight_continuousOn (compact : IsCompact (Set.univ : Set M)) :
    ContinuousOn (m65AreaWeight F) (Set.Icc a b) :=
  (areaComparisonPrimitive_continuousOn F compact).rexp



theorem m65AreaWeight_hasDerivWithinAt (compact : IsCompact (Set.univ : Set M))
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    HasDerivWithinAt (m65AreaWeight F)
      ((flowScalarCurvatureInfimum F t / 2) * m65AreaWeight F t) (Set.Icc a b) t := by
  change HasDerivWithinAt
    (fun r => Real.exp (∫ v in a..r, flowScalarCurvatureInfimum F v / 2))
    ((flowScalarCurvatureInfimum F t / 2) *
      Real.exp (∫ r in a..t, flowScalarCurvatureInfimum F r / 2)) (Set.Icc a b) t
  exact ((areaComparisonPrimitive_hasDerivWithinAt F compact ht).exp).congr_deriv (mul_comm _ _)

end PoincareConjecture
