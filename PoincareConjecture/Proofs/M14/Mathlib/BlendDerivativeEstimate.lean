import PoincareConjecture.Proofs.M09.SmoothJoinCutoff










set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M14

open Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem smoothJoinBlend_contDiffOn_one (f g : ℝ → E) (c d : ℝ) (U : Set ℝ)
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U) :
    ContDiffOn ℝ 1 (smoothJoinBlend f g c d) U := by
  exact hf.add (((smoothJoinCutoff_contDiff.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).comp
    ((contDiff_id.sub contDiff_const).div_const d)).contDiffOn.smul (hg.sub hf))




theorem smoothJoinBlend_deriv_sq_le (f g : ℝ → E) {c d s K : ℝ}
    (hd : 0 < d) (hK : 0 ≤ K)
    (hKb : ∀ r ∈ Icc (-1 : ℝ) 1, ‖deriv smoothJoinCutoff r‖ ≤ K)
    (hs : s ∈ Icc (c - d) (c + d))
    (hf : DifferentiableAt ℝ f s) (hg : DifferentiableAt ℝ g s) :
    ‖deriv (smoothJoinBlend f g c d) s‖ ^ 2 ≤
      12 * ‖deriv f s‖ ^ 2 + 3 * ‖deriv g s‖ ^ 2 +
        3 * (K / d) ^ 2 * ‖g s - f s‖ ^ 2 := by
  have harg : (s - c) / d ∈ Icc (-1 : ℝ) 1 :=
    ⟨(le_div_iff₀ hd).mpr (by linarith [hs.1]),
      (div_le_iff₀ hd).mpr (by linarith [hs.2])⟩
  have hchi : ‖smoothJoinCutoff ((s - c) / d)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (smoothJoinCutoff_mem _).1]
    exact (smoothJoinCutoff_mem _).2
  have hD : ‖deriv smoothJoinCutoff ((s - c) / d) / d‖ ≤ K / d := by
    rw [norm_div, Real.norm_of_nonneg hd.le]
    exact div_le_div_of_nonneg_right (hKb _ harg) hd.le
  have hterm : ‖(deriv smoothJoinCutoff ((s - c) / d) / d) • (g s - f s)‖ ≤
      (K / d) * ‖g s - f s‖ := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right hD (norm_nonneg _)
  have hlast : ‖smoothJoinCutoff ((s - c) / d) • (deriv g s - deriv f s)‖ ≤
      ‖deriv g s‖ + ‖deriv f s‖ := by
    rw [norm_smul]
    exact (mul_le_mul hchi (norm_sub_le _ _) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul _)
  have hnorm : ‖deriv (smoothJoinBlend f g c d) s‖ ≤
      2 * ‖deriv f s‖ + ‖deriv g s‖ + (K / d) * ‖g s - f s‖ := by
    rw [(smoothJoinBlend_hasDerivAt f g c d s hf hg).deriv]
    have hsum := norm_add_le (deriv f s)
      ((deriv smoothJoinCutoff ((s - c) / d) / d) • (g s - f s))
    have hsum' := norm_add_le
      (deriv f s + (deriv smoothJoinCutoff ((s - c) / d) / d) • (g s - f s))
      (smoothJoinCutoff ((s - c) / d) • (deriv g s - deriv f s))
    linarith
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm
  nlinarith [sq_nonneg (2 * ‖deriv f s‖ - ‖deriv g s‖),
    sq_nonneg (2 * ‖deriv f s‖ - (K / d) * ‖g s - f s‖),
    sq_nonneg (‖deriv g s‖ - (K / d) * ‖g s - f s‖)]

end PoincareConjecture.M14
