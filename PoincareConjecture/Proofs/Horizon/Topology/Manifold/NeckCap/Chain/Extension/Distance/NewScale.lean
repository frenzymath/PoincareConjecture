import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.BalancedDistance
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.FrontierScale

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.EpsilonNeck

theorem exists_balanced_frontier_distance_in_new_scale :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 10000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (N P : EpsilonNeck g),
        N.epsilon ≤ ε₀ → P.epsilon = N.epsilon → P.center ∈ frontier N.carrier →
        ENNReal.ofReal ((0.99 : ℝ) * P.scale * P.epsilon⁻¹) ≤ g.edist P.center N.center ∧
          g.edist P.center N.center ≤ ENNReal.ofReal ((1.01 : ℝ) * P.scale * P.epsilon⁻¹) := by
  obtain ⟨ε₁, hε₁, _, hscalar⟩ := exists_ambient_scalar_control_on_closure.{u}
    (α := 1 / 1000) (by norm_num)
  refine ⟨min ε₁ (1 / 10000), lt_min hε₁ (by norm_num), min_le_right _ _, ?_⟩
  intro M _ _ _ _ _ _ _ g N P hε heq hfront
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hsmall : N.epsilon ≤ 1 / 10000 := hε.trans (min_le_right _ _)
  have hc := abs_le.mp (hscalar N N.connection (hε.trans (min_le_left _ _))
    P.center (frontier_subset_closure hfront))
  have hnormal := P.scale_sq_mul_scalar_center_of_connection N.connection
  have hprod : P.scale ^ 2 * (N.scale ^ 2 * N.connection.scalarCurvature P.center) =
      N.scale ^ 2 := by
    calc
      _ = N.scale ^ 2 * (P.scale ^ 2 * N.connection.scalarCurvature P.center) := by ring
      _ = _ := by rw [hnormal, mul_one]
  have hsqlo : (0.999 : ℝ) * P.scale ^ 2 ≤ N.scale ^ 2 := by
    have h := mul_le_mul_of_nonneg_left
      (show (0.999 : ℝ) ≤ N.scale ^ 2 * N.connection.scalarCurvature P.center by
        linarith [hc.1]) (sq_nonneg P.scale)
    rw [hprod] at h
    nlinarith
  have hsqhi : N.scale ^ 2 ≤ (1.001 : ℝ) * P.scale ^ 2 := by
    have h := mul_le_mul_of_nonneg_left
      (show N.scale ^ 2 * N.connection.scalarCurvature P.center ≤ (1.001 : ℝ) by
        linarith [hc.2]) (sq_nonneg P.scale)
    rw [hprod] at h
    nlinarith
  have hlo : (0.999 : ℝ) * P.scale ≤ N.scale := by
    apply (sq_le_sq₀ (mul_nonneg (by norm_num) P.scale_pos.le) N.scale_pos.le).mp
    nlinarith [sq_nonneg P.scale]
  have hhi : N.scale ≤ (1.001 : ℝ) * P.scale := by
    apply (sq_le_sq₀ N.scale_pos.le (mul_nonneg (by norm_num) P.scale_pos.le)).mp
    nlinarith [sq_nonneg P.scale]
  have hrootlo : (0.999 : ℝ) ≤ Real.sqrt (1 - N.epsilon) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 - N.epsilon by linarith)
    nlinarith [Real.sqrt_nonneg (1 - N.epsilon)]
  have hroothi : Real.sqrt (1 + N.epsilon) ≤ (1.001 : ℝ) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 + N.epsilon by linarith [N.epsilon_pos])
    nlinarith [Real.sqrt_nonneg (1 + N.epsilon)]
  have hinv := inv_pos.mpr N.epsilon_pos
  have hinvlarge : (10000 : ℝ) ≤ N.epsilon⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hsmall hinv.le
    rw [mul_inv_cancel₀ N.epsilon_pos.ne'] at h
    linarith
  have hupper : 2 * Real.pi + Real.sqrt (1 + N.epsilon) * N.epsilon⁻¹ ≤
      (1.002 : ℝ) * N.epsilon⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hroothi hinv.le
    nlinarith [Real.pi_le_four]
  have hdist : g.edist P.center N.center = g.edist N.center P.center :=
    Manifold.riemannianEDist_comm
  rw [hdist, heq]
  constructor
  · apply (ENNReal.ofReal_le_ofReal ?_).trans
      (N.edist_center_lower_of_not_mem_carrier (N.carrier_open.frontier_eq ▸ hfront).2)
    apply mul_le_mul_of_nonneg_right _ hinv.le
    calc
      (0.99 : ℝ) * P.scale ≤ ((0.999 : ℝ) * P.scale) * (0.999 : ℝ) := by
        nlinarith [P.scale_pos]
      _ ≤ N.scale * Real.sqrt (1 - N.epsilon) :=
        mul_le_mul hlo hrootlo (by norm_num) N.scale_pos.le
  · apply (N.edist_center_le_model_bound_of_mem_closure
      (frontier_subset_closure hfront)).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ ((1.002 : ℝ) * N.epsilon⁻¹) * N.scale :=
        mul_le_mul_of_nonneg_right hupper N.scale_pos.le
      _ ≤ ((1.002 : ℝ) * N.epsilon⁻¹) * ((1.001 : ℝ) * P.scale) :=
        mul_le_mul_of_nonneg_left hhi (by positivity)
      _ ≤ _ := by nlinarith [mul_pos P.scale_pos hinv]

end PoincareConjecture.EpsilonNeck
