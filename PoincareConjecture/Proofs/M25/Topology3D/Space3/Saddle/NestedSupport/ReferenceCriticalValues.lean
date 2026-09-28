import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceHighCritical
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D

noncomputable section

theorem reference_critical_values_explicit
    (ws wm : ℝ)
    (hwslo : (1 : ℝ) / 2 < ws) (hwshi : ws < 3 / 4)
    (_hwsroot : (2 - 1 / ws) * Real.sqrt (1 - ws ^ 2) = 1 / 32)
    (hwmlo : 0 < wm) (hwmhi : wm < 1 / 2)
    (_hwmroot : (2 - 1 / wm) * Real.sqrt (1 - wm ^ 2) = -(1 / 32)) :
    let U : E2 → ℝ := fun v =>
      ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
    let vs : E2 := !₂[-Real.sqrt (1 - ws ^ 2), 0]
    let vm : E2 := !₂[Real.sqrt (1 - wm ^ 2), 0]
    let k : ℝ := U vs
    let mu : ℝ := U vm
    (37 : ℝ) / 32 < k → k < (5 : ℝ) / 4 → (5 : ℝ) / 4 < mu →
      k = 1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32 ∧
      mu = 1 - wm ^ 2 + wm + Real.sqrt (1 - wm ^ 2) / 32 ∧
      (17 : ℝ) / 16 < k ∧ k < mu := by
  dsimp only
  intro hK hKUpper hMu
  let vs : E2 := !₂[-Real.sqrt (1 - ws ^ 2), 0]
  let vm : E2 := !₂[Real.sqrt (1 - wm ^ 2), 0]
  have hNorm (v : E2) : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hwspos : 0 < ws := by linarith only [hwslo]
  have hwssq : 0 < 1 - ws ^ 2 := by nlinarith only [hwslo, hwshi]
  have hwmsq : 0 < 1 - wm ^ 2 := by nlinarith only [hwmlo, hwmhi]
  have hvssq : ‖vs‖ ^ 2 = 1 - ws ^ 2 := by
    rw [hNorm]
    change (-Real.sqrt (1 - ws ^ 2)) ^ 2 + (0 : ℝ) ^ 2 = _
    rw [neg_sq, Real.sq_sqrt hwssq.le]
    ring
  have hvmsq : ‖vm‖ ^ 2 = 1 - wm ^ 2 := by
    rw [hNorm]
    change (Real.sqrt (1 - wm ^ 2)) ^ 2 + (0 : ℝ) ^ 2 = _
    rw [Real.sq_sqrt hwmsq.le]
    ring
  have hvss : Real.sqrt (1 - ‖vs‖ ^ 2) = ws := by
    rw [hvssq, sub_sub_cancel, Real.sqrt_sq_eq_abs, abs_of_pos hwspos]
  have hvms : Real.sqrt (1 - ‖vm‖ ^ 2) = wm := by
    rw [hvmsq, sub_sub_cancel, Real.sqrt_sq_eq_abs, abs_of_pos hwmlo]
  have hK' : (37 : ℝ) / 32 <
      ‖vs‖ ^ 2 + Real.sqrt (1 - ‖vs‖ ^ 2) + vs 0 / 32 := by
    simpa [vs] using hK
  have hMu' : (5 : ℝ) / 4 <
      ‖vm‖ ^ 2 + Real.sqrt (1 - ‖vm‖ ^ 2) + vm 0 / 32 := by
    simpa [vm] using hMu
  have hKval : ‖vs‖ ^ 2 + Real.sqrt (1 - ‖vs‖ ^ 2) + vs 0 / 32 =
      1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32 := by
    change ‖vs‖ ^ 2 + Real.sqrt (1 - ‖vs‖ ^ 2) +
      (-Real.sqrt (1 - ws ^ 2)) / 32 = _
    rw [hvss, hvssq]
    ring
  have hMuval : ‖vm‖ ^ 2 + Real.sqrt (1 - ‖vm‖ ^ 2) + vm 0 / 32 =
      1 - wm ^ 2 + wm + Real.sqrt (1 - wm ^ 2) / 32 := by
    change ‖vm‖ ^ 2 + Real.sqrt (1 - ‖vm‖ ^ 2) +
      Real.sqrt (1 - wm ^ 2) / 32 = _
    rw [hvms, hvmsq]
  have hKexpr : (17 : ℝ) / 16 <
      ‖vs‖ ^ 2 + Real.sqrt (1 - ‖vs‖ ^ 2) + vs 0 / 32 := by
    exact (show (17 : ℝ) / 16 < 37 / 32 by norm_num).trans hK'
  have hKgap : (17 : ℝ) / 16 <
      1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32 := by
    have hKexpr' := hKexpr
    rw [hKval] at hKexpr'
    exact hKexpr'
  have hMugap :
      1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32 <
        1 - wm ^ 2 + wm + Real.sqrt (1 - wm ^ 2) / 32 := by
    have hKUpper' :
        ‖vs‖ ^ 2 + Real.sqrt (1 - ‖vs‖ ^ 2) + vs 0 / 32 < (5 : ℝ) / 4 := by
      simpa [vs] using hKUpper
    have hMuExpr : (5 : ℝ) / 4 <
        ‖vm‖ ^ 2 + Real.sqrt (1 - ‖vm‖ ^ 2) + vm 0 / 32 := hMu'
    rw [hKval] at hKUpper'
    rw [hMuval] at hMuExpr
    exact hKUpper'.trans hMuExpr
  have hRawGap :
      ‖vs‖ ^ 2 + Real.sqrt (1 - ‖vs‖ ^ 2) + vs 0 / 32 <
        ‖vm‖ ^ 2 + Real.sqrt (1 - ‖vm‖ ^ 2) + vm 0 / 32 := by
    have hKUpper' :
        ‖vs‖ ^ 2 + Real.sqrt (1 - ‖vs‖ ^ 2) + vs 0 / 32 < (5 : ℝ) / 4 := by
      simpa [vs] using hKUpper
    exact hKUpper'.trans hMu'
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [vs] using hKval
  · simpa [vm] using hMuval
  · simpa [vs] using hKexpr
  · simpa [vs, vm] using hRawGap

end
end PoincareConjecture.M25.Topology3D
