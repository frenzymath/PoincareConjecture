import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.Control
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.ScaleComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

theorem exists_ambient_scalar_control_on_closure {α : ℝ} (hα : 0 < α) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N : EpsilonNeck g) (D : LeviCivitaData g), N.epsilon ≤ ε₀ →
      ∀ x ∈ closure N.carrier, |N.scale ^ 2 * D.scalarCurvature x - 1| ≤ α := by
  obtain ⟨ε₀, hε₀, hsmall, hcontrol⟩ := exists_ambient_curvature_control.{u} hα
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N D hε x hx
  have hinterior (y : M) (hy : y ∈ N.carrier) :
      |N.scale ^ 2 * D.scalarCurvature y - 1| ≤ α := by
    have hs := (N.coordinate_inverse_mem y hy).2
    have h := (hcontrol N D hε (N.coordinate_inverse y).1 hs).1.le
    simpa only [Prod.eta, N.coordinate_map_coordinate_inverse hy] using h
  exact le_on_closure hinterior
    (((continuous_const.mul D.continuous_scalarCurvature).sub continuous_const).abs.continuousOn)
    continuous_const.continuousOn hx

theorem exists_scale_comparison_on_closure :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N N' : EpsilonNeck g), N.epsilon ≤ ε₀ →
      N'.center ∈ closure N.carrier →
      (0.99 : ℝ) * N.scale ≤ N'.scale ∧ N'.scale ≤ (1.01 : ℝ) * N.scale := by
  obtain ⟨ε₀, hε₀, hsmall, hcontrol⟩ :=
    exists_ambient_scalar_control_on_closure.{u} (α := 1 / 100) (by norm_num)
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N N' hε hcenter
  have hscalar := abs_le.mp (hcontrol N N.connection hε N'.center hcenter)
  have hnormal := N'.scale_sq_mul_scalar_center_of_connection N.connection
  have hprod : N'.scale ^ 2 *
      (N.scale ^ 2 * N.connection.scalarCurvature N'.center) = N.scale ^ 2 := by
    calc
      _ = N.scale ^ 2 * (N'.scale ^ 2 * N.connection.scalarCurvature N'.center) := by ring
      _ = N.scale ^ 2 := by rw [hnormal, mul_one]
  have hlower : (99 / 100 : ℝ) * N'.scale ^ 2 ≤ N.scale ^ 2 := by
    have h := mul_le_mul_of_nonneg_left
      (show (99 / 100 : ℝ) ≤ N.scale ^ 2 * N.connection.scalarCurvature N'.center by
        linarith [hscalar.1]) (sq_nonneg N'.scale)
    rw [hprod] at h
    nlinarith
  have hupper : N.scale ^ 2 ≤ (101 / 100 : ℝ) * N'.scale ^ 2 := by
    have h := mul_le_mul_of_nonneg_left
      (show N.scale ^ 2 * N.connection.scalarCurvature N'.center ≤ (101 / 100 : ℝ) by
        linarith [hscalar.2]) (sq_nonneg N'.scale)
    rw [hprod] at h
    nlinarith
  constructor
  · apply (sq_le_sq₀ (mul_nonneg (by norm_num) N.scale_pos.le) N'.scale_pos.le).mp
    nlinarith [sq_nonneg N'.scale]
  · apply (sq_le_sq₀ N'.scale_pos.le (mul_nonneg (by norm_num) N.scale_pos.le)).mp
    nlinarith [sq_nonneg N'.scale]

end PoincareConjecture.EpsilonNeck
