import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Models.RoundBounds
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.StandardGeometry.StandardNecks

/-!
# Universal primitive analytic bounds for the canonical models

Choose the Euclidean neck constants once, then instantiate the same
transport theorem on the physical Type-u carrier and the Type-0 standard
cap. Morgan--Tian Definition 2.16, equation (2.1), p. 30, Definition 2.18,
p. 31, and Definition 9.76, p. 231.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT.M45

/-- Positive universal neck and round constants yield every literal
primitive model field, including the explicit Type-0 standard-neck field.
Source: Definitions 2.16, 2.18 and 9.76, pp. 30-31 and 231. -/
theorem model_analytic_bounds_nonempty : Nonempty M45ModelAnalyticBounds.{u} := by
  obtain ⟨Cg, hCg, hgradient⟩ :=
    exists_model_scalar_differential_bound_of_coordinate_jets modelNeckCoordinateBound
  obtain ⟨Ce, hCe, hevolution⟩ := M44.exists_scalar_evolution_bound_of_coordinate_jets 3
    (show (0 : ℝ) < 1 / 2 by norm_num) modelNeckCoordinateBound
  obtain ⟨Cr, hCr, hround⟩ := exists_model_round_analytic_bound.{u}
  refine ⟨{
    neck_constant := max Cg Ce
    neck_constant_pos := lt_of_lt_of_le hCg (le_max_left _ _)
    round_constant := Cr
    round_constant_pos := hCr
    neck := ?_
    round := hround
    standard_neck := ?_
  }⟩
  · intro M _ _ _ g D N hsmall
    exact model_neck_analytic hCg hCe
      (fun gE DE => hgradient gE DE 0) (fun gE DE => hevolution gE DE 0) g D N hsmall
  · intro atlas g₀ F t epsilon x I N hsmall hzero
    exact model_neck_analytic hCg hCe
      (fun gE DE => hgradient gE DE 0) (fun gE DE => hevolution gE DE 0)
      (F.metric t) (F.connection t) (N.staticAtZero hzero).toEpsilonNeck hsmall

/-- The selected universal primitive model analytic bounds for M45.
The choice concerns numerical witnesses before any actual metric or flow.
Source: Definitions 2.16, 2.18 and 9.76, pp. 30-31 and 231. -/
noncomputable def modelAnalyticBounds : M45ModelAnalyticBounds.{u} :=
  Classical.choice model_analytic_bounds_nonempty

end PoincareMT.M45
