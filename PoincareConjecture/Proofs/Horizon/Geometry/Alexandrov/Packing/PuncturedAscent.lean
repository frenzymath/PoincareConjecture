import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Packing.PuncturedAngles
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Comparison.DistanceAscent










noncomputable section
set_option autoImplicit false

namespace Poincare.Alexandrov

theorem exists_pos_punctured_distance_ascent
    {X : Type*} [MetricSpace X]
    (hX : CurvatureGEnegOne X)
    (hgeo : ∀ x y : X, ∃ γ : ℝ → X, γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y)
    (hpacking : ∀ α : ℝ, 0 < α → ∃ N : ℕ, ComparisonAnglePackingBound X α N)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (p : X) :
    ∃ r : ℝ, 0 < r ∧ ∀ y : X, 0 < dist p y → dist p y < r →
      ∀ s : ℝ, 0 < s → ∃ z : X,
        dist y z < s ∧ c * dist y z < dist p z - dist p y := by
  let α := Real.arccos ((c + 1) / 2) / 2
  have hα : 0 < α := half_pos (Real.arccos_pos.mpr (by linarith))
  have hαpi : α < Real.pi / 2 := by
    exact div_lt_div_of_pos_right (Real.arccos_lt_pi.mpr (by linarith)) (by norm_num)
  have hcos : Real.cos (2 * α) = (c + 1) / 2 := by
    dsimp [α]
    rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    exact Real.cos_arccos (by linarith) (by linarith)
  obtain ⟨N, hN⟩ := hpacking α hα
  obtain ⟨r, hr, hnear⟩ := hN.exists_pos_near_opposite hα hαpi p
  refine ⟨r, hr, ?_⟩
  intro y hpy hyr
  obtain ⟨q, hqy, hangle⟩ := hnear y hpy hyr
  obtain ⟨γ, hγ0, hγ1, hγdist⟩ := hgeo y q
  apply hX.exists_local_distance_ascent_of_comparisonAngle (dist_pos.mp hpy) hqy
    γ hγ0 hγ1 hγdist hc0
  have hcoslt := Real.cos_lt_cos_of_nonneg_of_le_pi
    (by linarith : 0 ≤ Real.pi - 2 * α)
    (comparisonAngle_le_pi (dist y p) (dist y q) (dist p q)) hangle
  rw [Real.cos_pi_sub, hcos] at hcoslt
  linarith

end Poincare.Alexandrov
