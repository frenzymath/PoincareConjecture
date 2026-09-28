import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderUniformScalar










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28




theorem exists_neck_balanced_scale_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M]
        (g : RiemannianMetric 3 M) (_D : LeviCivitaData g)
        (N N' : EpsilonNeck g),
        N.epsilon ≤ epsilon₀ → N'.epsilon ≤ epsilon₀ →
        (N.carrier ∩ N'.carrier).Nonempty →
        (999 / 1000 : ℝ) * N'.scale < N.scale ∧
          N.scale < (1001 / 1000 : ℝ) * N'.scale := by
  obtain ⟨epsilon₀, hpos, hsmall, hclose⟩ :=
    tube.exists_cylinder_scalar_accuracy.{u} (delta := 1 / 1000000) (by norm_num)
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro M _ _ _ _ g D N N' hN hN' hmeet
  obtain ⟨x, hx, hx'⟩ := hmeet
  have hleft := abs_lt.mp (hclose M g D N hN x hx)
  have hright := abs_lt.mp (hclose M g D N' hN' x hx')
  have hprod : 0 < N.scale ^ 2 * D.scalarCurvature x := by linarith
  have hR : 0 < D.scalarCurvature x :=
    (mul_pos_iff.mp hprod).resolve_right (fun h => (not_lt_of_ge (sq_nonneg _) h.1)) |>.2
  have hsq : N.scale ^ 2 < (1001 / 1000 : ℝ) ^ 2 * N'.scale ^ 2 := by
    apply (mul_lt_mul_iff_right₀ hR).mp
    nlinarith only [hleft.2, hright.1]
  have hsq' : N'.scale ^ 2 < (1001 / 1000 : ℝ) ^ 2 * N.scale ^ 2 := by
    apply (mul_lt_mul_iff_right₀ hR).mp
    nlinarith only [hright.2, hleft.1]
  have hscale : N.scale < (1001 / 1000 : ℝ) * N'.scale := by
    nlinarith [N.scale_pos, N'.scale_pos]
  have hscale' : N'.scale < (1001 / 1000 : ℝ) * N.scale := by
    nlinarith [N.scale_pos, N'.scale_pos]
  exact ⟨by nlinarith [N.scale_pos, N'.scale_pos], hscale⟩

end PoincareConjecture.M28
