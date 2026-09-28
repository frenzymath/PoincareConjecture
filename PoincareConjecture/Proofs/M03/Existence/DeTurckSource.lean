import PoincareConjecture.Proofs.M03.Existence.DeTurckSymbol
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Ring.Real










set_option autoImplicit false

noncomputable section

namespace PoincareConjecture.DeTurckNative

variable {n : ℕ}

theorem symbol_add_of_symmetric (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ k l, G k l = G l k) (xi : Fin n → ℝ)
    (h k : Matrix (Fin n) (Fin n) ℝ)
    (hh : ∀ i j, h i j = h j i) (hk : ∀ i j, k i j = k j i) (i j : Fin n) :
    symbol G xi (h + k) i j = symbol G xi h i j + symbol G xi k i j := by
  rw [symbol_eq_quadratic G hG xi (h + k)
      (fun i j ↦ by simp [hh i j, hk i j]) i j,
    symbol_eq_quadratic G hG xi h hh i j,
    symbol_eq_quadratic G hG xi k hk i j]
  simp [Matrix.add_apply]
  ring

theorem symbol_smul_of_symmetric (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ k l, G k l = G l k) (xi : Fin n → ℝ)
    (a : ℝ) (h : Matrix (Fin n) (Fin n) ℝ)
    (hh : ∀ i j, h i j = h j i) (i j : Fin n) :
    symbol G xi (a • h) i j = a * symbol G xi h i j := by
  rw [symbol_eq_quadratic G hG xi (a • h)
      (fun i j ↦ by simp [hh i j]) i j,
    symbol_eq_quadratic G hG xi h hh i j]
  simp [Matrix.smul_apply, smul_eq_mul]
  ring

theorem continuous_symbol (G : Matrix (Fin n) (Fin n) ℝ) (xi : Fin n → ℝ)
    (i j : Fin n) :
    Continuous (fun h : Matrix (Fin n) (Fin n) ℝ => symbol G xi h i j) := by
  have hchrist (k i j : Fin n) :
      Continuous (fun h : Matrix (Fin n) (Fin n) ℝ =>
        christoffelSymbol G xi h k i j) := by
    unfold christoffelSymbol
    apply Continuous.mul continuous_const
    apply continuous_finsetSum
    intro l hl
    fun_prop
  have hdiv (j : Fin n) :
      Continuous (fun h : Matrix (Fin n) (Fin n) ℝ => divergence G xi h j) := by
    unfold divergence
    apply continuous_finsetSum
    intro k hk
    apply continuous_finsetSum
    intro l hl
    fun_prop
  have htrace :
      Continuous (fun h : Matrix (Fin n) (Fin n) ℝ => traceVariation G h) := by
    unfold traceVariation
    apply continuous_finsetSum
    intro k hk
    apply continuous_finsetSum
    intro l hl
    fun_prop
  have hone (j : Fin n) :
      Continuous (fun h : Matrix (Fin n) (Fin n) ℝ => oneFormSymbol G xi h j) := by
    unfold oneFormSymbol
    exact (hdiv j).sub (continuous_const.mul htrace)
  have hricci :
      Continuous (fun h : Matrix (Fin n) (Fin n) ℝ => ricciSymbol G xi h i j) := by
    unfold ricciSymbol
    apply Continuous.mul continuous_const
    apply continuous_finsetSum
    intro k hk
    exact (continuous_const.mul (hchrist k i j)).sub
      (continuous_const.mul (hchrist k i k))
  have hcorr :
      Continuous (fun h : Matrix (Fin n) (Fin n) ℝ => correctionSymbol G xi h i j) := by
    unfold correctionSymbol
    exact (continuous_const.mul (hone j)).add (continuous_const.mul (hone i))
  change Continuous ((fun h : Matrix (Fin n) (Fin n) ℝ => ricciSymbol G xi h i j) +
    (fun h : Matrix (Fin n) (Fin n) ℝ => correctionSymbol G xi h i j))
  exact hricci.add hcorr

theorem continuous_symbol_joint (i j : Fin n) :
    Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) ×
        Matrix (Fin n) (Fin n) ℝ => symbol p.1 p.2.1 p.2.2 i j) := by
  have hchrist (k i j : Fin n) :
      Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) ×
          Matrix (Fin n) (Fin n) ℝ =>
        christoffelSymbol p.1 p.2.1 p.2.2 k i j) := by
    unfold christoffelSymbol
    apply Continuous.mul continuous_const
    apply continuous_finsetSum
    intro l hl
    fun_prop
  have hdiv (j : Fin n) :
      Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) ×
          Matrix (Fin n) (Fin n) ℝ => divergence p.1 p.2.1 p.2.2 j) := by
    unfold divergence
    apply continuous_finsetSum
    intro k hk
    apply continuous_finsetSum
    intro l hl
    fun_prop
  have htrace :
      Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) ×
          Matrix (Fin n) (Fin n) ℝ => traceVariation p.1 p.2.2) := by
    unfold traceVariation
    apply continuous_finsetSum
    intro k hk
    apply continuous_finsetSum
    intro l hl
    fun_prop
  have hone (j : Fin n) :
      Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) ×
          Matrix (Fin n) (Fin n) ℝ => oneFormSymbol p.1 p.2.1 p.2.2 j) := by
    unfold oneFormSymbol
    exact (hdiv j).sub (by
      apply Continuous.mul
      · fun_prop
      · exact htrace)
  have hricci :
      Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) ×
          Matrix (Fin n) (Fin n) ℝ => ricciSymbol p.1 p.2.1 p.2.2 i j) := by
    unfold ricciSymbol
    apply Continuous.mul continuous_const
    apply continuous_finsetSum
    intro k hk
    exact (by
      apply Continuous.sub
      · apply Continuous.mul
        · fun_prop
        · exact hchrist k i j
      · apply Continuous.mul
        · fun_prop
        · exact hchrist k i k)
  have hcorr :
      Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) ×
          Matrix (Fin n) (Fin n) ℝ => correctionSymbol p.1 p.2.1 p.2.2 i j) := by
    unfold correctionSymbol
    apply Continuous.add <;> apply Continuous.mul <;> fun_prop
  change Continuous ((fun p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) ×
    Matrix (Fin n) (Fin n) ℝ => ricciSymbol p.1 p.2.1 p.2.2 i j) +
    (fun p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) ×
      Matrix (Fin n) (Fin n) ℝ => correctionSymbol p.1 p.2.1 p.2.2 i j))
  exact hricci.add hcorr



theorem continuous_symbol_matrix_joint :
    Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) ×
        Matrix (Fin n) (Fin n) ℝ => symbol p.1 p.2.1 p.2.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_symbol_joint i j

end PoincareConjecture.DeTurckNative

end
