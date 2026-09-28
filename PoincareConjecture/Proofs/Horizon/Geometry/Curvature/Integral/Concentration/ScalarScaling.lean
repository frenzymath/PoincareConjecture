import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Rescaling

noncomputable section
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture

theorem tendsto_rescaled_unitBall_scalar_integral_of_tendsto_ball_scalar_integral
    {n : ℕ} {M : ℕ → Type*}
    [∀ j, TopologicalSpace (M j)] [∀ j, T3Space (M j)]
    [∀ j, MeasurableSpace (M j)] [∀ j, BorelSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)]
    (g : ∀ j, RiemannianMetric n (M j)) (D : ∀ j, LeviCivitaData (g j))
    (p : ∀ j, M j) (r : ℕ → ℝ) (hn : 2 ≤ n) (hr : ∀ j, 0 < r j)
    (hr1 : ∀ᶠ j in atTop, r j ≤ 1)
    (hdiv : Tendsto (fun j => ∫ x in (g j).ball (p j) (r j),
      (D j).scalarCurvature x ∂(g j).volumeMeasure) atTop atTop) :
    let G := fun j => rescaledMetric (g j) (r j ^ 2)⁻¹
      (inv_pos.mpr (sq_pos_of_pos (hr j)))
    let DS := fun j => rescaledMetric_connection (g j) (D j) (r j ^ 2)⁻¹
      (inv_pos.mpr (sq_pos_of_pos (hr j)))
    Tendsto (fun j => ∫ x in (G j).ball (p j) 1,
      (DS j).scalarCurvature x ∂(G j).volumeMeasure) atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ hdiv
  filter_upwards [hdiv.eventually (eventually_ge_atTop 0), hr1] with j hj hj1
  have hfactor : 1 ≤ (r j ^ 2)⁻¹ :=
    (one_le_inv₀ (sq_pos_of_pos (hr j))).mpr (by nlinarith only [hr j, hj1])
  have hscale := rescaledMetric_integral_scalarCurvature_ball_mul
    (g j) (D j) hn (r j ^ 2)⁻¹ (inv_pos.mpr (sq_pos_of_pos (hr j))) (p j) (r j)
  have hs : Real.sqrt (r j ^ 2)⁻¹ * r j = 1 := by
    rw [Real.sqrt_inv, Real.sqrt_sq (hr j).le]
    exact inv_mul_cancel₀ (hr j).ne'
  rw [hs] at hscale
  rw [hscale]
  exact le_mul_of_one_le_left hj (one_le_pow₀ (Real.one_le_sqrt.mpr hfactor))

end PoincareConjecture
