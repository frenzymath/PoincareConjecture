import PoincareConjecture.Proofs.M03.Existence.ChartJetSource
import PoincareConjecture.Proofs.M03.Existence.DeTurckSymbol

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

namespace PoincareConjecture.DeTurckNative

variable {n : ℕ}

theorem secondJetSource_rankOne
    (G : Matrix (Fin n) (Fin n) ℝ) (xi : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    secondJetSource G
        (fun a b : Fin n => (xi a * xi b) • H) i j =
      quadratic G⁻¹ xi * H i j := by
  unfold secondJetSource quadratic
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem secondJetSource_rankOne_pos
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef)
    (xi : Fin n → ℝ) (hxi : xi ≠ 0)
    (H : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n)
    (hH : 0 < H i j) :
    0 < secondJetSource G
        (fun a b : Fin n => (xi a * xi b) • H) i j := by
  rw [secondJetSource_rankOne]
  exact mul_pos (quadratic_inv_pos G hG xi hxi) hH

end PoincareConjecture.DeTurckNative

end
