import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BoundaryGeometry
import Mathlib.Analysis.SpecialFunctions.Complex.Arg













noncomputable section
set_option autoImplicit false

open Set
open scoped ContDiff Matrix

namespace PoincareConjecture



theorem m64Intrinsic_boundary_periodic (radius : ℝ) :
    Function.Periodic (intrinsicAnnulusBoundary radius) rampPeriod := by
  intro s
  ext i
  fin_cases i
  · change radius * Real.cos (s + 2 * Real.pi) = radius * Real.cos s
    rw [Real.cos_add_two_pi]
  · change radius * Real.sin (s + 2 * Real.pi) = radius * Real.sin s
    rw [Real.sin_add_two_pi]




theorem m64Intrinsic_exists_boundary_parameter
    {x : AnnulusCoordinates} {radius : ℝ} (hnorm : ‖x‖ = radius) :
    ∃ b ∈ Ico (0 : ℝ) rampPeriod, x = intrinsicAnnulusBoundary radius b := by
  let z : ℂ := ⟨x 0, x 1⟩
  have hz : ‖z‖ = ‖x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg z) (norm_nonneg x)).mp
    simp only [Complex.sq_norm, Complex.normSq_apply, EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_two, z]
    ring
  have hparam : x = intrinsicAnnulusBoundary radius z.arg := by
    ext i
    fin_cases i
    · change x 0 = radius * Real.cos z.arg
      simpa only [hz, hnorm, z] using (Complex.norm_mul_cos_arg z).symm
    · change x 1 = radius * Real.sin z.arg
      simpa only [hz, hnorm, z] using (Complex.norm_mul_sin_arg z).symm
  by_cases hpos : 0 ≤ z.arg
  · refine ⟨z.arg, ⟨hpos, ?_⟩, hparam⟩
    unfold rampPeriod
    linarith [Complex.arg_le_pi z, Real.pi_pos]
  · refine ⟨z.arg + rampPeriod, ⟨?_, ?_⟩, ?_⟩
    · unfold rampPeriod
      linarith [Complex.neg_pi_lt_arg z, Real.pi_pos]
    · linarith [lt_of_not_ge hpos]
    · rw [(m64Intrinsic_boundary_periodic radius) z.arg]
      exact hparam

end PoincareConjecture
