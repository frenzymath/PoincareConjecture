import PoincareConjecture.Proofs.M25.Topology3D.Space3.HorizontalFieldLift










set_option autoImplicit false

open Set Metric
open scoped ContDiff NNReal

namespace PoincareConjecture.M25.Topology3D

variable {P : Type*} [NormedAddCommGroup P]



theorem norm_le_of_lipschitz_supported_ball (g : P → P) {L : ℝ≥0}
    (hg : LipschitzWith L g) (hg0 : g 0 = 0) {b : ℝ} (hb : 0 ≤ b)
    (hs : tsupport g ⊆ ball 0 b) (x : P) : ‖g x‖ ≤ L * b := by
  by_cases hx : x ∈ tsupport g
  · have h := hg.norm_sub_le x 0
    rw [hg0, sub_zero, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp (hs hx)).le L.coe_nonneg)
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
    exact mul_nonneg L.coe_nonneg hb

variable [NormedSpace ℝ P]



theorem horizontalFieldLift_lipschitz (χ : ℝ → ℝ) (g : P → P)
    {k l b : ℝ≥0} (hχ : LipschitzWith k χ) (hχnorm : ∀ r, ‖χ r‖ ≤ 1)
    (hg : LipschitzWith l g) (hgnorm : ∀ x, ‖g x‖ ≤ b) :
    LipschitzWith (l + k * b) (horizontalFieldLift χ g) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  change dist (χ p.2 • g p.1, (0 : ℝ)) (χ q.2 • g q.1, 0) ≤ _
  rw [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg), dist_eq_norm]
  have heq : χ p.2 • g p.1 - χ q.2 • g q.1 =
      χ p.2 • (g p.1 - g q.1) + (χ p.2 - χ q.2) • g q.1 := by module
  rw [heq]
  calc
    ‖χ p.2 • (g p.1 - g q.1) + (χ p.2 - χ q.2) • g q.1‖ ≤
        ‖χ p.2 • (g p.1 - g q.1)‖ + ‖(χ p.2 - χ q.2) • g q.1‖ := norm_add_le _ _
    _ = ‖χ p.2‖ * ‖g p.1 - g q.1‖ + ‖χ p.2 - χ q.2‖ * ‖g q.1‖ := by
      rw [norm_smul, norm_smul]
    _ ≤ 1 * (l * dist p.1 q.1) + (k * dist p.2 q.2) * b := add_le_add
      (mul_le_mul (hχnorm _) (by simpa only [dist_eq_norm] using hg.norm_sub_le p.1 q.1)
        (norm_nonneg _) zero_le_one)
      (mul_le_mul (by simpa only [dist_eq_norm] using hχ.norm_sub_le p.2 q.2)
        (hgnorm _) (norm_nonneg _) (by positivity))
    _ ≤ 1 * (l * dist p q) + (k * dist p q) * b := by
      gcongr
      · exact le_max_left _ _
      · exact le_max_right _ _
    _ = (l + k * b : ℝ≥0) * dist p q := by
      simp only [NNReal.coe_add, NNReal.coe_mul]
      ring

end PoincareConjecture.M25.Topology3D
