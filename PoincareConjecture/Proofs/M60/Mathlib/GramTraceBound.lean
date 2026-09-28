import PoincareConjecture.Proofs.M60.Mathlib.GramDeterminantDerivative
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace PoincareConjecture.M60

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem abs_inverse_gram_contraction_le (v : Fin 2 → E)
    (B : LinearMap.BilinForm ℝ E) {D : ℝ}
    (hbound : ∀ q : E, |B q q| ≤ D * inner ℝ q q)
    (hdet : 0 < Matrix.det (Matrix.gram ℝ v)) :
    |∑ i : Fin 2, ∑ j : Fin 2, ((Matrix.gram ℝ v)⁻¹) i j * B (v j) (v i)| ≤ 2 * D := by
  let a := inner ℝ (v 0) (v 0)
  let b := inner ℝ (v 0) (v 1)
  let c := inner ℝ (v 1) (v 1)
  let delta := a * c - b ^ 2
  have h10 : inner ℝ (v 1) (v 0) = b := real_inner_comm _ _
  have hdelta : 0 < delta := by
    simpa only [Matrix.det_fin_two, Matrix.gram_apply, real_inner_comm (v 1) (v 0),
      a, b, c, delta, pow_two] using hdet
  have ha : 0 < a := by
    have hnonneg : 0 ≤ a := real_inner_self_nonneg
    by_contra h
    have ha0 : a = 0 := le_antisymm (le_of_not_gt h) hnonneg
    have : delta ≤ 0 := by
      simpa only [delta, ha0, zero_mul, zero_sub, neg_nonpos] using sq_nonneg b
    exact (not_lt_of_ge this) hdelta
  let w := v 1 - (b / a) • v 0
  have hww : inner ℝ w w = delta / a := by
    simp only [w, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    rw [h10]
    change c - b / a * b - (b / a * b - b / a * (b / a * a)) = delta / a
    dsimp only [delta]
    field_simp
    ring
  have hBww : B w w = B (v 1) (v 1) - b / a * B (v 0) (v 1) -
      b / a * B (v 1) (v 0) + (b / a) ^ 2 * B (v 0) (v 0) := by
    simp only [w, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  have htrace : (∑ i : Fin 2, ∑ j : Fin 2,
      ((Matrix.gram ℝ v)⁻¹) i j * B (v j) (v i)) =
      B (v 0) (v 0) / a + a / delta * B w w := by
    rw [inverse_contraction_fin_two (Matrix.gram ℝ v) (fun i j => B (v i) (v j))]
    simp only [Matrix.det_fin_two, Matrix.gram_apply, h10]
    rw [hBww]
    change (B (v 0) (v 0) * c + a * B (v 1) (v 1) - B (v 0) (v 1) * b -
      b * B (v 1) (v 0)) / (a * c - b * b) = _
    rw [← pow_two b]
    change (B (v 0) (v 0) * c + a * B (v 1) (v 1) - B (v 0) (v 1) * b -
      b * B (v 1) (v 0)) / delta = _
    field_simp [ha.ne', hdelta.ne']
    dsimp only [delta]
    ring
  have hfirst : |B (v 0) (v 0) / a| ≤ D := by
    rw [abs_div, abs_of_pos ha]
    exact (div_le_iff₀ ha).mpr (hbound (v 0))
  have hsecond : |a / delta * B w w| ≤ D := by
    rw [abs_mul, abs_of_pos (div_pos ha hdelta)]
    have h := mul_le_mul_of_nonneg_left (hbound w) (div_pos ha hdelta).le
    rw [hww] at h
    calc
      a / delta * |B w w| ≤ a / delta * (D * (delta / a)) := h
      _ = D := by field_simp
  rw [htrace]
  exact (abs_add_le _ _).trans (by linarith)

end PoincareConjecture.M60
