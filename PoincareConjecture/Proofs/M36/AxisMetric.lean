import PoincareConjecture.Proofs.M36.StandardRotations
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum









set_option autoImplicit false

namespace PoincareConjecture.M36

noncomputable def axisPoint (r : ℝ) : StandardCapSpace :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![r, 0, 0]

noncomputable def axisBasis (i : Fin 3) : StandardCapSpace :=
  EuclideanSpace.single i 1

def axisHalfTurn : Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨!![1, 0, 0; 0, -1, 0; 0, 0, -1], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
    · rw [Matrix.det_fin_three]
      change (1 : ℝ) * (-1) * (-1) - 1 * 0 * 0 - 0 * 0 * (-1) +
        0 * 0 * 0 + 0 * 0 * 0 - 0 * (-1) * 0 = 1
      norm_num⟩

def axisQuarterTurn : Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨!![1, 0, 0; 0, 0, -1; 0, 1, 0], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
    · rw [Matrix.det_fin_three]
      change (1 : ℝ) * 0 * 0 - 1 * (-1) * 1 - 0 * 0 * 0 +
        0 * (-1) * 0 + 0 * 0 * 1 - 0 * 0 * 0 = 1
      norm_num⟩

theorem axisHalfTurn_point (r : ℝ) : standardRotation axisHalfTurn (axisPoint r) =
    axisPoint r := by
  ext i
  fin_cases i <;>
    simp [standardRotation, axisHalfTurn, axisPoint, dotProduct,
      Fin.sum_univ_succ]

theorem axisQuarterTurn_point (r : ℝ) : standardRotation axisQuarterTurn (axisPoint r) =
    axisPoint r := by
  ext i
  fin_cases i <;>
    simp [standardRotation, axisQuarterTurn, axisPoint, dotProduct,
      Fin.sum_univ_succ]

theorem axisHalfTurn_basis_zero : standardRotation axisHalfTurn (axisBasis 0) =
    axisBasis 0 := by
  ext i
  fin_cases i <;>
    simp [standardRotation, axisHalfTurn, axisBasis, EuclideanSpace.single,
      dotProduct]

theorem axisHalfTurn_basis_one : standardRotation axisHalfTurn (axisBasis 1) =
    -axisBasis 1 := by
  ext i
  fin_cases i <;>
    simp [standardRotation, axisHalfTurn, axisBasis, EuclideanSpace.single,
      dotProduct]

theorem axisHalfTurn_basis_two : standardRotation axisHalfTurn (axisBasis 2) =
    -axisBasis 2 := by
  ext i
  fin_cases i <;>
    simp [standardRotation, axisHalfTurn, axisBasis, EuclideanSpace.single,
      dotProduct]

theorem axisQuarterTurn_basis_one : standardRotation axisQuarterTurn (axisBasis 1) =
    axisBasis 2 := by
  ext i
  fin_cases i <;>
    simp [standardRotation, axisQuarterTurn, axisBasis, EuclideanSpace.single,
      dotProduct]

theorem axisQuarterTurn_basis_two : standardRotation axisQuarterTurn (axisBasis 2) =
    -axisBasis 1 := by
  ext i
  fin_cases i <;>
    simp [standardRotation, axisQuarterTurn, axisBasis, EuclideanSpace.single,
      dotProduct]

theorem axis_metric_zero_one (g₀ : StandardInitialMetric) (r : ℝ) :
    g₀.metric.inner (axisPoint r) (axisBasis 0) (axisBasis 1) = 0 := by
  have h := g₀.rotation_invariant axisHalfTurn (axisPoint r) (axisBasis 0) (axisBasis 1)
  simp only [standardRotation_mfderiv] at h
  change g₀.metric.inner (standardRotation axisHalfTurn (axisPoint r))
      (standardRotation axisHalfTurn (axisBasis 0))
      (standardRotation axisHalfTurn (axisBasis 1)) = _ at h
  rw [axisHalfTurn_point, axisHalfTurn_basis_zero, axisHalfTurn_basis_one] at h
  let B : StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ :=
    g₀.metric.inner (axisPoint r)
  change B (axisBasis 0) (-axisBasis 1) = B (axisBasis 0) (axisBasis 1) at h
  rw [map_neg] at h
  change B (axisBasis 0) (axisBasis 1) = 0
  linarith

theorem axis_metric_zero_two (g₀ : StandardInitialMetric) (r : ℝ) :
    g₀.metric.inner (axisPoint r) (axisBasis 0) (axisBasis 2) = 0 := by
  have h := g₀.rotation_invariant axisHalfTurn (axisPoint r) (axisBasis 0) (axisBasis 2)
  simp only [standardRotation_mfderiv] at h
  change g₀.metric.inner (standardRotation axisHalfTurn (axisPoint r))
      (standardRotation axisHalfTurn (axisBasis 0))
      (standardRotation axisHalfTurn (axisBasis 2)) = _ at h
  rw [axisHalfTurn_point, axisHalfTurn_basis_zero, axisHalfTurn_basis_two] at h
  let B : StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ :=
    g₀.metric.inner (axisPoint r)
  change B (axisBasis 0) (-axisBasis 2) = B (axisBasis 0) (axisBasis 2) at h
  rw [map_neg] at h
  change B (axisBasis 0) (axisBasis 2) = 0
  linarith

theorem axis_metric_one_two (g₀ : StandardInitialMetric) (r : ℝ) :
    g₀.metric.inner (axisPoint r) (axisBasis 1) (axisBasis 2) = 0 := by
  have h := g₀.rotation_invariant axisQuarterTurn (axisPoint r) (axisBasis 1) (axisBasis 2)
  simp only [standardRotation_mfderiv] at h
  change g₀.metric.inner (standardRotation axisQuarterTurn (axisPoint r))
      (standardRotation axisQuarterTurn (axisBasis 1))
      (standardRotation axisQuarterTurn (axisBasis 2)) = _ at h
  rw [axisQuarterTurn_point, axisQuarterTurn_basis_one, axisQuarterTurn_basis_two] at h
  let B : StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ :=
    g₀.metric.inner (axisPoint r)
  change B (axisBasis 2) (-axisBasis 1) = B (axisBasis 1) (axisBasis 2) at h
  rw [map_neg] at h
  have hsymm : B (axisBasis 2) (axisBasis 1) = B (axisBasis 1) (axisBasis 2) :=
    g₀.metric.symm _ _ _
  rw [hsymm] at h
  change B (axisBasis 1) (axisBasis 2) = 0
  linarith

theorem axis_metric_tangential_eq (g₀ : StandardInitialMetric) (r : ℝ) :
    g₀.metric.inner (axisPoint r) (axisBasis 1) (axisBasis 1) =
      g₀.metric.inner (axisPoint r) (axisBasis 2) (axisBasis 2) := by
  have h := g₀.rotation_invariant axisQuarterTurn (axisPoint r) (axisBasis 1) (axisBasis 1)
  simp only [standardRotation_mfderiv] at h
  change g₀.metric.inner (standardRotation axisQuarterTurn (axisPoint r))
      (standardRotation axisQuarterTurn (axisBasis 1))
      (standardRotation axisQuarterTurn (axisBasis 1)) = _ at h
  rw [axisQuarterTurn_point, axisQuarterTurn_basis_one] at h
  exact h.symm

end PoincareConjecture.M36
