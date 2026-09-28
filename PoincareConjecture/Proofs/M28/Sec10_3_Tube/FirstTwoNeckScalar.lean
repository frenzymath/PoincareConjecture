import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderUniformScalar

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

theorem exists_initial_pair_scalar_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
        (N Q : EpsilonNeck g), N.epsilon ≤ epsilon₀ →
        Q.epsilon = N.epsilon → (0.999 : ℝ) * N.scale < Q.scale →
        ∀ x ∈ N.carrier ∪ Q.carrier,
          D.scalarCurvature x ≤ 4 * D.scalarCurvature N.center := by
  obtain ⟨epsilon₀, hpos, hsmall, hratio⟩ :=
    tube.exists_cylinder_scalar_ratio_accuracy.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro M _ _ _ _ g D N Q hε hQε hscale x hx
  have hNpos : 0 < D.scalarCurvature N.center := by
    rw [← N.connection.scalarCurvature_eq_m28 D N.center]
    exact N.scalar_center_pos
  have hQpos : 0 < D.scalarCurvature Q.center := by
    rw [← Q.connection.scalarCurvature_eq_m28 D Q.center]
    exact Q.scalar_center_pos
  have hNnorm := tube.neck_normalized_scalar_center N D
  have hQnorm := tube.neck_normalized_scalar_center Q D
  have hscaleSq : N.scale ^ 2 ≤ 2 * Q.scale ^ 2 := by
    have hsq := (sq_lt_sq₀
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.999) N.scale_pos.le)
      Q.scale_pos.le).mpr hscale
    nlinarith only [hsq, sq_nonneg N.scale]
  have hcenter : D.scalarCurvature Q.center ≤ 2 * D.scalarCurvature N.center := by
    have h := mul_le_mul_of_nonneg_right hscaleSq hQpos.le
    apply (mul_le_mul_iff_right₀ (pow_pos N.scale_pos 2)).mp
    nlinarith only [h, hNnorm, hQnorm]
  rcases hx with hx | hx
  · have h := hratio M g D N hε x hx N.center
      (N.central_sphere_subset N.center_on_central_sphere)
    linarith only [h, hNpos]
  · have h := hratio M g D Q (by rw [hQε]; exact hε) x hx Q.center
      (Q.central_sphere_subset Q.center_on_central_sphere)
    linarith only [h, hcenter]

end PoincareConjecture.M28
