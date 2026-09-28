import PoincareConjecture.Definitions.Ch18.Deformation

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {t₀ t₁ : ℝ} (F : RicciFlow 3 M (Set.Icc t₀ t₁))

@[simp] theorem areaComparisonProfile_initial (a : ℝ) :
    areaComparisonProfile F a t₀ = a := by
  simp [areaComparisonProfile]

theorem areaComparisonProfile_sub (a b t : ℝ) :
    areaComparisonProfile F a t - areaComparisonProfile F b t =
      Real.exp (-(∫ s in t₀..t, flowScalarCurvatureInfimum F s / 2)) * (a - b) := by
  unfold areaComparisonProfile flowScalarCurvatureInfimum
  ring

theorem areaComparisonProfile_add (a error t : ℝ) :
    areaComparisonProfile F (a + error) t = areaComparisonProfile F a t +
      Real.exp (-(∫ s in t₀..t, flowScalarCurvatureInfimum F s / 2)) * error := by
  unfold areaComparisonProfile flowScalarCurvatureInfimum
  ring

theorem areaComparisonProfile_strictMono (t : ℝ) :
    StrictMono (fun a => areaComparisonProfile F a t) := by
  intro a b hab
  unfold areaComparisonProfile
  exact mul_lt_mul_of_pos_left (sub_lt_sub_right hab _) (Real.exp_pos _)

theorem areaComparisonProfile_mono (t : ℝ) :
    Monotone (fun a => areaComparisonProfile F a t) :=
  (areaComparisonProfile_strictMono F t).monotone

theorem abs_areaComparisonProfile_sub (a b t : ℝ) :
    |areaComparisonProfile F a t - areaComparisonProfile F b t| =
      Real.exp (-(∫ s in t₀..t, flowScalarCurvatureInfimum F s / 2)) * |a - b| := by
  rw [areaComparisonProfile_sub, abs_mul, abs_of_pos (Real.exp_pos _)]

end PoincareConjecture
