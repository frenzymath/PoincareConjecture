import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_NeckBuffer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_neck_containment_cutoff {K D : ℝ} (hK : 0 < K) (hD : 0 < D) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧
      ∀ {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M]
        {g : RiemannianMetric 3 M} (N : EpsilonNeck g), N.epsilon ≤ epsilon0 →
      ∀ h : ℝ, 0 < h → N.connection.scalarCurvature N.center * h ^ 2 ≤ K →
      ∀ p ∈ N.central_sphere, g.ball p (h * D) ⊆ N.carrier := by
  have hsqrt : 0 < Real.sqrt (2 * K) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨min (1 / 12) (1 / (4 * D * Real.sqrt (2 * K))),
    lt_min (by norm_num) (by positivity), ?_⟩
  intro M _ _ _ _ g N hsmall h hh hscale p hp
  have heps := hsmall.trans (min_le_left _ _)
  have hsize := hsmall.trans (min_le_right _ _)
  let c := (1 - 6 * N.epsilon) / N.connection.scalarCurvature N.center
  have hc : 0 < c := div_pos (by linarith) N.scalar_center_pos
  have hsquare : (h / Real.sqrt (2 * K)) ^ 2 ≤ c := by
    rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * K)]
    change h ^ 2 / (2 * K) ≤ (1 - 6 * N.epsilon) / N.connection.scalarCurvature N.center
    rw [div_le_div_iff₀ (by positivity : 0 < 2 * K) N.scalar_center_pos]
    have hprod := mul_nonneg hK.le (show 0 ≤ 1 / 2 - 6 * N.epsilon by linarith)
    nlinarith
  have hsqrtc : h / Real.sqrt (2 * K) ≤ Real.sqrt c := by
    nlinarith [Real.sq_sqrt hc.le, Real.sqrt_nonneg c, div_pos hh hsqrt]
  have hinv : 4 * D * Real.sqrt (2 * K) ≤ N.epsilon⁻¹ := by
    have hmul := (le_div_iff₀ (by positivity : 0 < 4 * D * Real.sqrt (2 * K))).mp hsize
    rw [inv_eq_one_div, le_div_iff₀ N.epsilon_pos]
    nlinarith
  have hwidth : 2 * D * Real.sqrt (2 * K) ≤ N.epsilon⁻¹ / 2 := by linarith
  have hradius : h * D < Real.sqrt c * (N.epsilon⁻¹ / 2) := by
    calc
      h * D < 2 * h * D := by nlinarith [mul_pos hh hD]
      _ = (h / Real.sqrt (2 * K)) * (2 * D * Real.sqrt (2 * K)) := by
        field_simp
      _ ≤ Real.sqrt c * (N.epsilon⁻¹ / 2) :=
        mul_le_mul hsqrtc hwidth (by positivity) (Real.sqrt_nonneg c)
  intro y hy
  apply neck_ball_subset_carrier N heps hp
  exact hy.trans_le (ENNReal.ofReal_le_ofReal hradius.le)

end PoincareConjecture.M44
