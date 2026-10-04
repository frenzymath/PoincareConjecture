import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
Adapted from Mapher `PoincareMT/Proofs/M49/Mathlib/GramDensity.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Uniform volume-density tolerances

Morgan-Tian Definition 2.16, p. 30, controls the normalized metric
coefficients. The continuous square-root determinant gives a uniform
density comparison, used in Lemma 17.12, p. 410.
-/

set_option autoImplicit false

open Set

namespace Matrix

open scoped Classical in
/-- Uniform entrywise closeness to the identity controls Gram density,
as used in MT Definition 2.16, p. 30, and Lemma 17.12, p. 410. -/
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

/-- Entrywise closeness to any fixed positive density preserves half
that density (MT Definition 2.16, p. 30; Lemma 17.12, p. 410). -/
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
