import PoincareConjecture.Proofs.M35.Uniqueness.RotationStabilizer









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff Bundle Matrix Topology

namespace PoincareConjecture.M35.Uniqueness

theorem standardRotation_norm (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (x : StandardCapSpace) : ‖standardRotation A x‖ = ‖x‖ := by
  have h := standardRotation_inner A x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (standardRotation A x), norm_nonneg x]

theorem exists_coordinate_rotation_decomposition
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ a b c : ℝ, A = (coordinateRotation a * coordinateRotation02 b) * coordinateRotation c := by
  let z : StandardCapSpace := EuclideanSpace.single 2 1
  have hz : ‖standardRotation A z‖ = 1 := by
    rw [standardRotation_norm]
    simp [z, EuclideanSpace.single]
  obtain ⟨a, b, hab⟩ := exists_two_coordinate_rotations_axis (standardRotation A z) hz
  let Q := coordinateRotation a * coordinateRotation02 b
  have hQ : standardRotation Q z = standardRotation A z := hab
  have hfix : standardRotation (Q⁻¹ * A) z = z := by
    rw [standardRotation_mul, ← hQ, ← standardRotation_mul, inv_mul_cancel, standardRotation_one]
  obtain ⟨c, hc⟩ := exists_coordinateRotation_of_fixes_axis (Q⁻¹ * A) hfix
  refine ⟨a, b, c, ?_⟩
  change A = Q * coordinateRotation c
  rw [← hc, ← mul_assoc, mul_inv_cancel, one_mul]

theorem rotation_invariant_of_coordinate_killing
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (h01 : ∀ x u v : StandardCapSpace, DeTurckNative.metricLieDerivative D
      (fun y => coordinateRotationGenerator y) x u v = 0)
    (h02 : ∀ x u v : StandardCapSpace, DeTurckNative.metricLieDerivative D
      (fun y => coordinateRotation02Generator y) x u v = 0) :
    ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v := by
  intro A x u v
  rw [standardRotation_mfderiv]
  change g.euclideanCoefficients (standardRotation A x)
    (standardRotation A u) (standardRotation A v) = g.euclideanCoefficients x u v
  obtain ⟨a, b, c, rfl⟩ := exists_coordinate_rotation_decomposition A
  simp only [standardRotation_mul]
  exact (coordinateRotation_isometry_of_killing D h01 a _ _ _).trans
    ((coordinateRotation02_isometry_of_killing D h02 b _ _ _).trans
      (coordinateRotation_isometry_of_killing D h01 c x u v))

end PoincareConjecture.M35.Uniqueness
