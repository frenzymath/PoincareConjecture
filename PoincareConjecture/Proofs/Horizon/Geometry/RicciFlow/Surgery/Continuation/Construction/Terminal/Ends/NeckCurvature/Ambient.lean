import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.NeckCurvature.RealizationScalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.Ambient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.ScaleComparison

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem abs_scaled_scalar_sub_one_lt_half
    (N : EpsilonNeck g) (D : LeviCivitaData g) (hε : N.epsilon ≤ 1 / 200)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    |N.scale ^ 2 * D.scalarCurvature (N.coordinate_map (q, s)) - 1| < 1 / 2 := by
  obtain ⟨h, Dh, heq⟩ := N.exists_normalizedEuclideanCoefficients_realization q hs
  have hscalar := N.abs_realization_scalar_sub_one_lt_half hε q hs h Dh heq
  rw [(N.normalized_realization_curvature D q hs Dh heq).1] at hscalar
  exact hscalar

theorem abs_scaled_scalar_sub_one_lt_half_on_carrier
    (N : EpsilonNeck g) (D : LeviCivitaData g) (hε : N.epsilon ≤ 1 / 200)
    {x : M} (hx : x ∈ N.carrier) :
    |N.scale ^ 2 * D.scalarCurvature x - 1| < 1 / 2 := by
  have hs := (N.coordinate_inverse_mem x hx).2
  have h := N.abs_scaled_scalar_sub_one_lt_half D hε (N.coordinate_inverse x).1 hs
  have hmap := N.coordinate_map_eq
    ((N.coordinate_inverse x).1, ⟨(N.coordinate_inverse x).2, hs⟩)
  rw [N.coordinate_inverse_right x hx] at hmap
  rw [← hmap] at h
  exact h

theorem scalar_within_factor_two_on_carrier
    (N : EpsilonNeck g) (D : LeviCivitaData g) (hε : N.epsilon ≤ 1 / 200)
    {x : M} (hx : x ∈ N.carrier) :
    D.scalarCurvature N.center / 2 ≤ D.scalarCurvature x ∧
      D.scalarCurvature x ≤ 2 * D.scalarCurvature N.center := by
  have hc := abs_lt.mp (N.abs_scaled_scalar_sub_one_lt_half_on_carrier D hε hx)
  have hn := N.scale_sq_mul_scalar_center_of_connection D
  have hscale := sq_pos_of_pos N.scale_pos
  constructor
  · apply (mul_le_mul_iff_right₀ hscale).mp
    nlinarith only [hc.1, hn]
  · apply (mul_le_mul_iff_right₀ hscale).mp
    nlinarith only [hc.2, hn]

theorem abs_scaled_scalar_sub_one_lt_third
    (N : EpsilonNeck g) (D : LeviCivitaData g) (hε : N.epsilon ≤ 1 / 200)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    |N.scale ^ 2 * D.scalarCurvature (N.coordinate_map (q, s)) - 1| < 1 / 3 := by
  obtain ⟨h, Dh, heq⟩ := N.exists_normalizedEuclideanCoefficients_realization q hs
  have hscalar := N.abs_realization_scalar_sub_one_lt_third hε q hs h Dh heq
  rw [(N.normalized_realization_curvature D q hs Dh heq).1] at hscalar
  exact hscalar

theorem abs_scaled_scalar_sub_one_lt_third_on_carrier
    (N : EpsilonNeck g) (D : LeviCivitaData g) (hε : N.epsilon ≤ 1 / 200)
    {x : M} (hx : x ∈ N.carrier) :
    |N.scale ^ 2 * D.scalarCurvature x - 1| < 1 / 3 := by
  have hs := (N.coordinate_inverse_mem x hx).2
  have h := N.abs_scaled_scalar_sub_one_lt_third D hε (N.coordinate_inverse x).1 hs
  have hmap := N.coordinate_map_eq
    ((N.coordinate_inverse x).1, ⟨(N.coordinate_inverse x).2, hs⟩)
  rw [N.coordinate_inverse_right x hx] at hmap
  rw [← hmap] at h
  exact h

theorem scalar_lt_two_mul_of_mem_carrier
    (N : EpsilonNeck g) (D : LeviCivitaData g) (hε : N.epsilon ≤ 1 / 200)
    {x y : M} (hx : x ∈ N.carrier) (hy : y ∈ N.carrier) :
    D.scalarCurvature x < 2 * D.scalarCurvature y := by
  have hupper := (abs_lt.mp (N.abs_scaled_scalar_sub_one_lt_third_on_carrier D hε hx)).2
  have hlower := (abs_lt.mp (N.abs_scaled_scalar_sub_one_lt_third_on_carrier D hε hy)).1
  apply (mul_lt_mul_iff_right₀ (sq_pos_of_pos N.scale_pos)).mp
  nlinarith only [hupper, hlower]

end PoincareConjecture.EpsilonNeck
