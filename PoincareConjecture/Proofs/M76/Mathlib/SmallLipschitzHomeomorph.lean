import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

set_option autoImplicit false

open Set
open scoped NNReal

theorem LipschitzWith.exists_homeomorph_add {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {u : E → E} {L : ℝ≥0} (hu : LipschitzWith L u) (hL : L < 1) :
    ∃ H : E ≃ₜ E, ∀ x, H x = x + u x := by
  let e := ContinuousLinearEquiv.refl ℝ E
  have ha : ApproximatesLinearOn (fun x => x + u x) (e : E →L[ℝ] E) univ L := by
    intro x _ y _
    change ‖x + u x - (y + u y) - (x - y)‖ ≤ (L : ℝ) * ‖x - y‖
    rw [show x + u x - (y + u y) - (x - y) = u x - u y by abel]
    exact hu.norm_sub_le x y
  have hsmall : Subsingleton E ∨ L < ‖(e.symm : E →L[ℝ] E)‖₊⁻¹ := by
    rcases subsingleton_or_nontrivial E with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa [e] using hL)
  exact ⟨ha.toHomeomorph (fun x => x + u x) hsmall, fun _ => rfl⟩

theorem LipschitzWith.antilipschitzWith_id_add_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → E} {L : ℝ≥0} (hu : LipschitzWith L u) {t : ℝ}
    (ht : |t| * (L : ℝ) ≤ 1 / 2) :
    AntilipschitzWith 2 (fun x => x + t • u x) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  have herror : ‖t • (u x - u y)‖ ≤ (1 / 2 : ℝ) * ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ |t| * ((L : ℝ) * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (hu.norm_sub_le x y) (abs_nonneg t)
      _ ≤ _ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right ht (norm_nonneg _)
  have htri : ‖x - y‖ ≤ ‖(x + t • u x) - (y + t • u y)‖ + ‖t • (u x - u y)‖ := by
    calc
      _ = ‖((x + t • u x) - (y + t • u y)) - t • (u x - u y)‖ := by
        congr 1
        simp only [smul_sub]
        abel
      _ ≤ _ := _root_.norm_sub_le _ _
  simp only [dist_eq_norm, NNReal.coe_ofNat]
  linarith
