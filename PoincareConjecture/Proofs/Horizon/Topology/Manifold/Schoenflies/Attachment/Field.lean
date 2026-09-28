import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension













set_option autoImplicit false

open Set Metric
open scoped ContDiff

namespace Poincare.Manifold.Schoenflies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]



theorem exists_vertical_graph_field
    (b : E -> Real) (hb : ContDiff Real ∞ b) (hbc : HasCompactSupport b) :
    ∃ R : Real, 0 < R ∧ ∃ V : E × Real -> E × Real,
      ContDiff Real ∞ V ∧
      (∀ p, (V p).1 = 0) ∧
      (∀ p ∉ tsupport b ×ˢ closedBall (0 : Real) R, V p = 0) ∧
      ∀ x t, t ∈ Icc (0 : Real) 1 -> V (x, t * b x) = (0, b x) := by
  obtain ⟨C, hC⟩ := (hbc.image hb.continuous).isBounded.exists_norm_le
  let M := |C| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hbM (x : E) : |b x| ≤ M := by
    by_cases hx : x ∈ tsupport b
    · have h := hC _ (mem_image_of_mem b hx)
      change |b x| ≤ C at h
      exact h.trans ((le_abs_self C).trans (by dsimp [M]; linarith))
    · have hz : b x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hz, abs_zero]
      exact hM.le
  let chi : ContDiffBump (0 : Real) := ⟨M, M + 1, hM, lt_add_one M⟩
  let V : E × Real -> E × Real := fun p => (0, b p.1 * chi p.2)
  refine ⟨M + 1, by linarith, V,
    contDiff_const.prodMk ((hb.comp contDiff_fst).mul (chi.contDiff.comp contDiff_snd)),
    fun _ => rfl, ?_, ?_⟩
  · intro p hp
    by_cases hx : p.1 ∈ tsupport b
    · have hz : p.2 ∉ closedBall (0 : Real) (M + 1) := fun hz => hp ⟨hx, hz⟩
      have he : chi p.2 = 0 := chi.zero_of_le_dist (le_of_lt (not_le.mp hz))
      simp [V, he]
    · simp [V, image_eq_zero_of_notMem_tsupport hx]
  · intro x t ht
    have hnorm : t * b x ∈ closedBall (0 : Real) M := by
      rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg ht.1]
      calc
        t * |b x| ≤ 1 * |b x| := mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _)
        _ ≤ M := by simpa using hbM x
    simp [V, chi.one_of_mem_closedBall hnorm]

end Poincare.Manifold.Schoenflies
