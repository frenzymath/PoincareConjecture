import PoincareLib.Geometry.RicciFlow.Extinction.Width.Deformation.Family

/-!
# The initial-area dependence of the comparison profile

The initial-value identity and the second formula of Morgan--Tian Claim
18.26, printed p. 434, for the literal profile of Definition 18.23, p. 433.
These algebraic identities do not require regularity of the scalar infimum.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {t₀ t₁ : ℝ} (F : RicciFlow 3 M (Set.Icc t₀ t₁))

/-- Definition 18.23, p. 433: the displayed profile has the stated initial
value, including when the two endpoints of an interval integral coincide. -/
@[simp] theorem areaComparisonProfile_initial (a : ℝ) :
    areaComparisonProfile F a t₀ = a := by
  simp [areaComparisonProfile]

/-- Claim 18.26, p. 434: differences of initial values are multiplied by
the positive integrating factor. This identity holds for arbitrary values. -/
theorem areaComparisonProfile_sub (a b t : ℝ) :
    areaComparisonProfile F a t - areaComparisonProfile F b t =
      Real.exp (-(∫ s in t₀..t, flowScalarCurvatureInfimum F s / 2)) * (a - b) := by
  unfold areaComparisonProfile flowScalarCurvatureInfimum
  ring

/-- Claim 18.26, p. 434: the exact response to an additive initial error. -/
theorem areaComparisonProfile_add (a error t : ℝ) :
    areaComparisonProfile F (a + error) t = areaComparisonProfile F a t +
      Real.exp (-(∫ s in t₀..t, flowScalarCurvatureInfimum F s / 2)) * error := by
  unfold areaComparisonProfile flowScalarCurvatureInfimum
  ring

/-- Claim 18.26, p. 434: the terminal profile is strictly increasing in
the initial area; positivity is supplied by the exponential. -/
theorem areaComparisonProfile_strictMono (t : ℝ) :
    StrictMono (fun a => areaComparisonProfile F a t) := by
  intro a b hab
  unfold areaComparisonProfile
  exact mul_lt_mul_of_pos_left (sub_lt_sub_right hab _) (Real.exp_pos _)

/-- The weak monotonicity consequence of Claim 18.26, printed p. 434. -/
theorem areaComparisonProfile_mono (t : ℝ) :
    Monotone (fun a => areaComparisonProfile F a t) :=
  (areaComparisonProfile_strictMono F t).monotone

/-- Absolute-error form of Claim 18.26, p. 434, for transferring the
initial filling-area approximation into a terminal comparison estimate. -/
theorem abs_areaComparisonProfile_sub (a b t : ℝ) :
    |areaComparisonProfile F a t - areaComparisonProfile F b t| =
      Real.exp (-(∫ s in t₀..t, flowScalarCurvatureInfimum F s / 2)) * |a - b| := by
  rw [areaComparisonProfile_sub, abs_mul, abs_of_pos (Real.exp_pos _)]

end PoincareMT
