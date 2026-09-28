import PoincareConjecture.Proofs.M35.Uniqueness.InitialKilling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Matrix

namespace PoincareConjecture.M35.Uniqueness

noncomputable def coordinateRotation (s : ℝ) :
    Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨!![Real.cos s, -Real.sin s, 0;
      Real.sin s, Real.cos s, 0;
      0, 0, 1], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ] <;>
        nlinarith [Real.sin_sq_add_cos_sq s]
    · simp [Matrix.det_fin_three]
      nlinarith [Real.sin_sq_add_cos_sq s]⟩

theorem coordinateRotation_zero : coordinateRotation 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coordinateRotation]

noncomputable def coordinateRotationGenerator :
    StandardCapSpace →L[ℝ] StandardCapSpace :=
  (Matrix.toEuclideanLin !![(0 : ℝ), -1, 0; 1, 0, 0; 0, 0, 0]).toContinuousLinearMap

theorem coordinateRotation_hasDerivAt (x : StandardCapSpace) :
    HasDerivAt (fun s => standardRotation (coordinateRotation s) x)
      (coordinateRotationGenerator x) 0 := by
  let f : ℝ → Fin 3 → ℝ := fun s =>
    ![Real.cos s * x 0 - Real.sin s * x 1,
      Real.sin s * x 0 + Real.cos s * x 1, x 2]
  have hf : HasDerivAt f ![-x 1, x 0, 0] 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [f] using! ((Real.hasDerivAt_cos 0).mul_const (x 0)).sub
        ((Real.hasDerivAt_sin 0).mul_const (x 1))
    · simpa [f] using! ((Real.hasDerivAt_sin 0).mul_const (x 0)).add
        ((Real.hasDerivAt_cos 0).mul_const (x 1))
    · simpa [f] using hasDerivAt_const (0 : ℝ) (x 2)
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have h := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hf
  convert! h using 1
  · funext s
    ext i
    fin_cases i <;>
      simp [standardRotation, coordinateRotation, f, L,
        dotProduct, Fin.sum_univ_succ, sub_eq_add_neg]
  · ext i
    fin_cases i <;>
      simp [coordinateRotationGenerator, L, Matrix.toEuclideanLin,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem initial_coordinateRotationGenerator_killing (g₀ : StandardInitialMetric)
    (x u v : StandardCapSpace) :
    DeTurckNative.metricLieDerivative g₀.connection
      (fun y => coordinateRotationGenerator y) x u v = 0 :=
  initial_rotation_path_killing g₀ coordinateRotation coordinateRotationGenerator
    coordinateRotation_zero coordinateRotation_hasDerivAt x u v

end PoincareConjecture.M35.Uniqueness
