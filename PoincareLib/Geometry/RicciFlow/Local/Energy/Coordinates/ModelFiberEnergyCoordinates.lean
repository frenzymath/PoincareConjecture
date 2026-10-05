/- Adapted from Mapher `PoincareMT/Proofs/M03/ModelFiberEnergyCoordinates.lean` at
f927d9e1f0810042766d3b5f64d3f4da02ee93cc. See
`references/ricci-flow/mapher/local-theory/port.json`. -/

import PoincareLib.Geometry.Riemannian.Connection

/-!
# Fixed Euclidean coordinates for model-fiber energies

Equal finite dimensions give a continuous linear equivalence. The operator
bounds for it and its inverse compare the original norm squared with the
sum of squared Euclidean coordinates, including the zero-dimensional case.
Derivation: proof-work/tasks/M03/reviews/model-fiber-energy-coordinates-derivation.md.
-/

set_option autoImplicit false
open scoped BigOperators

universe u

namespace PoincareMT.RicciFlow.Local

theorem exists_model_fiber_energy_coordinates
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] :
    ∃ q : F ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ F)),
      ∃ C : ℝ, 0 < C ∧ ∀ v : F,
        (‖v‖ ^ 2 ≤ C * ∑ i, (q v i) ^ 2) ∧
        ((∑ i, (q v i) ^ 2) ≤ C * ‖v‖ ^ 2) := by
  let q : F ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ F)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let A : ℝ := ‖q.toContinuousLinearMap‖
  let B : ℝ := ‖q.symm.toContinuousLinearMap‖
  let C : ℝ := 1 + A ^ 2 + B ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hAC : A ^ 2 ≤ C := by dsimp [C]; nlinarith [sq_nonneg B]
  have hBC : B ^ 2 ≤ C := by dsimp [C]; nlinarith [sq_nonneg A]
  refine ⟨q, C, hC, ?_⟩
  intro v
  rw [← EuclideanSpace.real_norm_sq_eq]
  have hq : ‖q v‖ ≤ A * ‖v‖ := q.toContinuousLinearMap.le_opNorm v
  have hqi : ‖v‖ ≤ B * ‖q v‖ := by
    have h := q.symm.toContinuousLinearMap.le_opNorm (q v)
    change ‖q.symm (q v)‖ ≤ B * ‖q v‖ at h
    rw [q.symm_apply_apply] at h
    exact h
  constructor
  · calc
      ‖v‖ ^ 2 ≤ (B * ‖q v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hqi 2
      _ = B ^ 2 * ‖q v‖ ^ 2 := mul_pow _ _ _
      _ ≤ C * ‖q v‖ ^ 2 := mul_le_mul_of_nonneg_right hBC (sq_nonneg _)
  · calc
      ‖q v‖ ^ 2 ≤ (A * ‖v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hq 2
      _ = A ^ 2 * ‖v‖ ^ 2 := mul_pow _ _ _
      _ ≤ C * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hAC (sq_nonneg _)

end PoincareMT.RicciFlow.Local
