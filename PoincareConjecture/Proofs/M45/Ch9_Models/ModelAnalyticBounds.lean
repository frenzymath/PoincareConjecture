import PoincareConjecture.Proofs.M45.Ch9_Models.RoundBounds
import PoincareConjecture.Proofs.M45.Ch12_Standard.StandardNecks

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M45

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

noncomputable def modelAnalyticBounds : M45ModelAnalyticBounds.{u} :=
  Classical.choice model_analytic_bounds_nonempty

end PoincareConjecture.M45
