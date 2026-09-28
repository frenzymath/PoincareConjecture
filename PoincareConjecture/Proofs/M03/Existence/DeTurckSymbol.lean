import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

namespace PoincareConjecture.DeTurckNative

variable {n : ℕ}

def quadratic (G : Matrix (Fin n) (Fin n) ℝ) (xi : Fin n → ℝ) : ℝ :=
  ∑ k, ∑ l, G k l * xi k * xi l

def traceVariation (G h : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ k, ∑ l, G k l * h k l

def divergence (G : Matrix (Fin n) (Fin n) ℝ) (xi : Fin n → ℝ)
    (h : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : ℝ :=
  ∑ k, ∑ l, G k l * xi k * h l j

def christoffelSymbol (G : Matrix (Fin n) (Fin n) ℝ) (xi : Fin n → ℝ)
    (h : Matrix (Fin n) (Fin n) ℝ) (k i j : Fin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ l, G k l * (xi i * h j l + xi j * h i l - xi l * h i j)

def ricciSymbol (G : Matrix (Fin n) (Fin n) ℝ) (xi : Fin n → ℝ)
    (h : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : ℝ :=
  -2 * ∑ k, (xi k * christoffelSymbol G xi h k i j -
    xi j * christoffelSymbol G xi h k i k)

def oneFormSymbol (G : Matrix (Fin n) (Fin n) ℝ) (xi : Fin n → ℝ)
    (h : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : ℝ :=
  divergence G xi h j - (1 / 2 : ℝ) * xi j * traceVariation G h

def correctionSymbol (G : Matrix (Fin n) (Fin n) ℝ) (xi : Fin n → ℝ)
    (h : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : ℝ :=
  xi i * oneFormSymbol G xi h j + xi j * oneFormSymbol G xi h i

def symbol (G : Matrix (Fin n) (Fin n) ℝ) (xi : Fin n → ℝ)
    (h : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ ricciSymbol G xi h i j + correctionSymbol G xi h i j

private theorem christoffel_trace (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ k l, G k l = G l k) (xi : Fin n → ℝ)
    (h : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (∑ k, christoffelSymbol G xi h k i k) =
      (1 / 2 : ℝ) * xi i * traceVariation G h := by
  have hswap : (∑ k, ∑ l, G k l * xi k * h i l) =
      ∑ k, ∑ l, G k l * xi l * h i k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    rw [hG l k]
  calc
    _ = (1 / 2 : ℝ) * (xi i * traceVariation G h +
        (∑ k, ∑ l, G k l * xi k * h i l) -
        (∑ k, ∑ l, G k l * xi l * h i k)) := by
      simp only [christoffelSymbol, traceVariation, Finset.mul_sum,
        ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = _ := by rw [hswap]; ring

private theorem christoffel_contraction (G : Matrix (Fin n) (Fin n) ℝ)
    (xi : Fin n → ℝ) (h : Matrix (Fin n) (Fin n) ℝ)
    (hh : ∀ i j, h i j = h j i) (i j : Fin n) :
    (∑ k, xi k * christoffelSymbol G xi h k i j) =
      (1 / 2 : ℝ) * (xi i * divergence G xi h j +
        xi j * divergence G xi h i - quadratic G xi * h i j) := by
  simp only [christoffelSymbol, divergence, quadratic, Finset.mul_sum,
    Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [hh j l, hh i l]
  ring

private theorem ricciSymbol_eq (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ k l, G k l = G l k) (xi : Fin n → ℝ)
    (h : Matrix (Fin n) (Fin n) ℝ) (hh : ∀ i j, h i j = h j i)
    (i j : Fin n) :
    ricciSymbol G xi h i j = quadratic G xi * h i j -
      xi i * divergence G xi h j - xi j * divergence G xi h i +
      xi i * xi j * traceVariation G h := by
  rw [ricciSymbol, Finset.sum_sub_distrib, ← Finset.mul_sum,
    christoffel_trace G hG xi h i, christoffel_contraction G xi h hh i j]
  ring

theorem symbol_eq_quadratic (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ k l, G k l = G l k) (xi : Fin n → ℝ)
    (h : Matrix (Fin n) (Fin n) ℝ) (hh : ∀ i j, h i j = h j i)
    (i j : Fin n) :
    symbol G xi h i j = quadratic G xi * h i j := by
  rw [symbol, ricciSymbol_eq G hG xi h hh i j, correctionSymbol,
    oneFormSymbol, oneFormSymbol]
  ring

theorem symbol_isSymm (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ k l, G k l = G l k) (xi : Fin n → ℝ)
    (h : Matrix (Fin n) (Fin n) ℝ) (hh : ∀ i j, h i j = h j i) :
    Matrix.IsSymm (symbol G xi h) := by
  apply Matrix.IsSymm.ext
  intro i j
  rw [symbol_eq_quadratic G hG xi h hh j i,
    symbol_eq_quadratic G hG xi h hh i j, hh j i]

theorem quadratic_eq_dotProduct (G : Matrix (Fin n) (Fin n) ℝ)
    (xi : Fin n → ℝ) : quadratic G xi =
      dotProduct (Star.star xi) (Matrix.mulVec G xi) := by
  simp only [quadratic, dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem quadratic_pos (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef)
    (xi : Fin n → ℝ) (hxi : xi ≠ 0) : 0 < quadratic G xi := by
  rw [quadratic_eq_dotProduct]
  exact hG.dotProduct_mulVec_pos hxi

theorem quadratic_inv_pos (g : Matrix (Fin n) (Fin n) ℝ) (hg : g.PosDef)
    (xi : Fin n → ℝ) (hxi : xi ≠ 0) : 0 < quadratic g⁻¹ xi := by
  exact quadratic_pos g⁻¹ hg.inv xi hxi

end PoincareConjecture.DeTurckNative

end
