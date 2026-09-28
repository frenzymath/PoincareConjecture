import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNeckScalar
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNeckSets

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

theorem scale_sq_mul_scalar_center : N.scale ^ 2 * N.connection.scalarCurvature N.center = 1 := by
  rw [N.scale_eq_scalar, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
    Real.rpow_neg N.scalar_center_pos.le, ← Real.sqrt_eq_rpow, inv_pow,
    Real.sq_sqrt N.scalar_center_pos.le, inv_mul_cancel₀ N.scalar_center_pos.ne']

end PoincareConjecture.EpsilonNeck

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)

theorem boundary_scale_le_of_scalar_error
    (hR : ∀ x ∈ N.boundary_sphere,
      |N.end_neck.scale ^ 2 * N.connection.scalarCurvature x - 1| ≤ 1 / 10) :
    N.boundary_neck.scale ≤ (9 / 8 : ℝ) * N.end_neck.scale := by
  have hx : N.boundary_neck.center ∈ N.boundary_sphere := by
    rw [N.boundary_eq_neck_sphere]
    exact N.boundary_neck.center_on_central_sphere
  have hlow := (abs_le.mp (hR _ hx)).1
  have hnorm := N.boundary_neck.scale_sq_mul_scalar_center
  rw [N.boundary_neck_connection] at hnorm
  have hm := mul_le_mul_of_nonneg_right hlow (sq_nonneg N.boundary_neck.scale)
  have he : N.end_neck.scale ^ 2 *
      (N.boundary_neck.scale ^ 2 * N.connection.scalarCurvature N.boundary_neck.center) =
        N.end_neck.scale ^ 2 := by rw [hnorm, mul_one]
  have hs : (9 / 10 : ℝ) * N.boundary_neck.scale ^ 2 ≤ N.end_neck.scale ^ 2 := by
    nlinarith [hm, he]
  by_contra hnot
  have hd := sub_pos.mpr (lt_of_not_ge hnot)
  have hp := mul_pos hd (add_pos N.boundary_neck.scale_pos
    (mul_pos (by norm_num : (0 : ℝ) < 9 / 8) N.end_neck.scale_pos))
  nlinarith [sq_pos_of_pos N.end_neck.scale_pos]

end PoincareConjecture.CapCertificate

namespace PoincareConjecture.M34

theorem capPersistence_exists_cap_boundary_accuracy :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T3Space M]
        (g : RiemannianMetric 3 M) (N : CapCertificate g), N.epsilon < delta0 →
        (∀ x ∈ N.boundary_sphere,
          |N.end_neck.scale ^ 2 * N.connection.scalarCurvature x - 1| ≤ 1 / 10) ∧
        N.boundary_neck.scale ≤ (9 / 8 : ℝ) * N.end_neck.scale := by
  obtain ⟨delta0, hdelta0, hbound⟩ :=
    capPersistence_exists_neck_scalar_accuracy (by norm_num : (0 : ℝ) < 1 / 10)
  refine ⟨delta0, hdelta0, ?_⟩
  intro M _ _ _ _ _ _ g N hN
  let : T25Space M := T3Space.t25Space
  let : T2Space M := T25Space.t2Space
  have he : N.end_neck.epsilon < delta0 := by rwa [N.end_neck_epsilon]
  have hclose := (hbound M g N.end_neck he).2
  have hR : ∀ x ∈ N.boundary_sphere,
      |N.end_neck.scale ^ 2 * N.connection.scalarCurvature x - 1| ≤ 1 / 10 := by
    intro x hx
    have hxclose : x ∈ closure N.end_neck.carrier :=
      closure_mono (fun _ hy => hy.1) (N.boundary_subset_negative_end_closure hx)
    have h := hclose x hxclose
    rwa [N.end_neck_connection] at h
  exact ⟨hR, N.boundary_scale_le_of_scalar_error hR⟩

end PoincareConjecture.M34
