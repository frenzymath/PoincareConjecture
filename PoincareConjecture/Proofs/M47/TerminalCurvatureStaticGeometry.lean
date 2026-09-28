import PoincareConjecture.Proofs.M47.TerminalCurvatureNormContinuity
import PoincareConjecture.Definitions.M45SmallNecks
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M47


theorem terminalCurvature_compact_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hcompact : IsCompact (univ : Set M)) :
    ∃ B : ℝ, 0 < B ∧ ∀ x, D.curvatureTensorNorm x ≤ B := by
  obtain ⟨B, hB⟩ := hcompact.bddAbove_image (terminalCurvature_norm_continuous D).continuousOn
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x
  exact (hB (mem_image_of_mem D.curvatureTensorNorm (mem_univ x))).trans (le_max_right _ _)


theorem terminalCurvature_neck_scalar_le_of_scale
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    {scale0 : ℝ} (hscale0 : 0 < scale0) (hscale : scale0 ≤ N.scale) :
    N.connection.scalarCurvature N.center ≤ scale0⁻¹ ^ 2 := by
  have hnormalize : N.scale⁻¹ ^ 2 = N.connection.scalarCurvature N.center := by
    rw [N.scale_eq_scalar, inv_pow,
      ← Real.rpow_mul_natCast N.scalar_center_pos.le (-1 / 2) 2]
    norm_num [Real.rpow_neg_one]
  rw [← hnormalize]
  exact pow_le_pow_left₀ (inv_nonneg.mpr N.scale_pos.le)
    ((inv_le_inv₀ N.scale_pos hscale0).mpr hscale) 2



theorem terminalCurvature_cap_scalar_comparison
    {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : CapCertificate g)
    {x : M} (hx : x ∈ N.core) :
    N.connection.scalarCurvature x ≤
      N.cap_constant * N.end_neck.connection.scalarCurvature N.end_neck.center := by
  have hxclosed : x ∈ N.closed_core :=
    interior_subset (N.core_eq_interior_closed_core ▸ hx)
  have hxcarrier : x ∈ N.carrier := by
    rw [N.closed_core_eq_complement_end] at hxclosed
    exact hxclosed.1
  have hend : N.end_neck.center ∈ N.carrier :=
    N.end_neck_subset (N.end_neck.central_sphere_subset N.end_neck.center_on_central_sphere)
  obtain ⟨b, hb, hratio⟩ := N.scalar_ratio
  rw [N.end_neck_connection]
  exact (hratio _ hend _ hxcarrier).trans
    (mul_le_mul_of_nonneg_right hb.le (N.scalar_pos _ hend).le)

end PoincareConjecture.M47
