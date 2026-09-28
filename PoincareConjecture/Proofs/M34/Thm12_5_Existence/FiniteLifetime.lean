import PoincareConjecture.Proofs.M34.Thm12_5_Existence.PositiveScalarComparison

set_option autoImplicit false

open Set

namespace PoincareConjecture.M34

theorem partialFlow_lifetime_le_scalar_bound (P : RicciFlowCurvatureTheory.{0})
    {g0 : StandardInitialMetric} (E0 : StandardCapEstimate g0)
    (F : PartialStandardCapFlow g0) :
    F.lifetime ≤ 3 / (2 * E0.scalar_constant⁻¹) := by
  let a := E0.scalar_constant⁻¹
  have ha : 0 < a := inv_pos.mpr E0.scalar_constant_pos
  let B := 3 / (2 * a)
  have hB : 0 < B := div_pos (by norm_num) (mul_pos (by norm_num) ha)
  by_contra hno
  have hBF : B < F.lifetime := lt_of_not_ge hno
  obtain ⟨K, hK, hfull⟩ := F.curvature_locally_bounded B hB.le hBF
  let M := 9 * K
  have hM : 0 ≤ M := mul_nonneg (by norm_num) hK
  have hden : 0 < a + M + 1 := by positivity
  let t := B * (M + 1) / (a + M + 1)
  have ht : 0 < t := div_pos (mul_pos hB (by positivity)) hden
  have htB : t < B := by
    apply (div_lt_iff₀ hden).mpr
    exact mul_lt_mul_of_pos_left (by linarith) hB
  have hcancel : (2 * a / 3) * B = 1 := by
    dsimp [B]
    field_simp
  have hsmall : (2 * a / 3) * t < 1 := by
    exact (mul_lt_mul_of_pos_left htB (by positivity)).trans_eq hcancel
  have hdeneq : 1 - (2 * a / 3) * t = a / (a + M + 1) := by
    dsimp only [t, B]
    field_simp [ne_of_gt ha, ne_of_gt hden]
    ring
  have hvalue : a / (1 - (2 * a / 3) * t) = a + M + 1 := by
    rw [hdeneq]
    field_simp [ne_of_gt ha]
  have hcomp := partialFlow_positive_scalar_comparison P E0 F ha ht (htB.trans hBF)
    hsmall (fun x => (E0.scalar_bounds x).1) t ⟨ht.le, le_rfl⟩ 0
  rw [hvalue] at hcomp
  have hscalar := M10.abs_scalarCurvature_le (F.flow.metric t) (F.flow.connection t) 0
  norm_num only [Nat.cast_ofNat, show (3 : ℝ) ^ 2 = 9 by norm_num] at hscalar
  have hupper : (F.flow.connection t).scalarCurvature 0 ≤ M :=
    (le_abs_self _).trans (hscalar.trans (mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (hfull t ⟨ht.le, htB.le⟩ 0)) (by norm_num)))
  linarith

end PoincareConjecture.M34
