import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.Pseudo.Pi

set_option autoImplicit false

open Set

namespace Matrix

open scoped Classical in

theorem exists_pos_entrywise_sqrt_det_bounds (ι : Type*) [Fintype ι] :
    ∃ eta : ℝ, 0 < eta ∧ ∀ A : Matrix ι ι ℝ,
      (∀ i j, |A i j - if i = j then 1 else 0| ≤ eta) →
        (1 / 2 : ℝ) ≤ Real.sqrt A.det ∧ Real.sqrt A.det ≤ 2 := by
  classical
  have hc : Continuous (fun A : ι → ι → ℝ => Real.sqrt (Matrix.det A)) :=
    Real.continuous_sqrt.comp continuous_id.matrix_det
  obtain ⟨d, hd, hbound⟩ := (Metric.continuousAt_iff (α := ι → ι → ℝ)).mp
    (hc.continuousAt (x := (1 : Matrix ι ι ℝ)))
    (1 / 2) (by norm_num)
  refine ⟨d / 2, half_pos hd, ?_⟩
  intro A hA
  have hdist : dist (show ι → ι → ℝ from A) (1 : Matrix ι ι ℝ) ≤ d / 2 := by
    apply (dist_pi_le_iff (half_pos hd).le).mpr
    intro i
    apply (dist_pi_le_iff (half_pos hd).le).mpr
    intro j
    simpa only [Real.dist_eq, Matrix.one_apply] using hA i j
  have hb := hbound (show dist (show ι → ι → ℝ from A) (1 : Matrix ι ι ℝ) < d by
    linarith)
  simp only [Matrix.det_one, Real.sqrt_one, Real.dist_eq] at hb
  have hb' := abs_lt.mp hb
  constructor <;> linarith

theorem exists_pos_entrywise_sqrt_det_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : 0 < Real.sqrt A.det) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ B : Matrix ι ι ℝ,
      (∀ i j, |B i j - A i j| ≤ eta) →
        Real.sqrt A.det / 2 ≤ Real.sqrt B.det := by
  have hc : Continuous (fun B : ι → ι → ℝ => Real.sqrt (Matrix.det B)) :=
    Real.continuous_sqrt.comp continuous_id.matrix_det
  obtain ⟨d, hd, hbound⟩ := (Metric.continuousAt_iff (α := ι → ι → ℝ)).mp
    (hc.continuousAt (x := A)) (Real.sqrt A.det / 2) (half_pos hA)
  refine ⟨d / 2, half_pos hd, ?_⟩
  intro B hB
  have hdist : dist (show ι → ι → ℝ from B) A ≤ d / 2 := by
    apply (dist_pi_le_iff (half_pos hd).le).mpr
    intro i
    apply (dist_pi_le_iff (half_pos hd).le).mpr
    intro j
    simpa only [Real.dist_eq] using hB i j
  have hb := hbound (show dist (show ι → ι → ℝ from B) A < d by linarith)
  rw [Real.dist_eq, abs_lt] at hb
  linarith [hb.1]

end Matrix
