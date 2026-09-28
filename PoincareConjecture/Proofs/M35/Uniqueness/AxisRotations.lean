import PoincareConjecture.Proofs.M35.Uniqueness.InitialKilling
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Matrix

namespace PoincareConjecture.M35.Uniqueness

private noncomputable abbrev axisUnit : StandardCapSpace := EuclideanSpace.single 2 1

private theorem matrix_action_mul (A B : Matrix (Fin 3) (Fin 3) ℝ)
    (x : StandardCapSpace) :
    Matrix.toEuclideanLin (A * B) x =
      Matrix.toEuclideanLin A (Matrix.toEuclideanLin B x) := by
  change WithLp.toLp 2 ((A * B) *ᵥ x.ofLp) =
    WithLp.toLp 2 (A *ᵥ (B *ᵥ x.ofLp))
  rw [Matrix.mulVec_mulVec]



theorem exists_axis_rotation (x : StandardCapSpace) :
    ∃ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      standardRotation A (‖x‖ • axisUnit) = x := by
  let u := ‖x‖ • axisUnit
  have hu : ‖u‖ = ‖x‖ := by
    simp [u, axisUnit, norm_smul]
  let L := (ℝ ∙ (u - x))ᗮ.reflection
  have hL : L u = x := Submodule.reflection_sub hu
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let M := L.toMatrix b.toBasis b.toBasis
  have hM : M ∈ Matrix.orthogonalGroup (Fin 3) ℝ := L.toMatrix_mem_unitaryGroup b b
  have haction : Matrix.toEuclideanLin M = L.toLinearEquiv.toLinearMap := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact Matrix.toLin_toMatrix _ _ _
  have hdet : M.det = 1 ∨ M.det = -1 := by
    rw [← sq_eq_one_iff]
    simpa [pow_two] using (Matrix.det_of_mem_unitary hM).2
  rcases hdet with hp | hn
  · refine ⟨⟨M, Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨hM, hp⟩⟩, ?_⟩
    change Matrix.toEuclideanLin M u = x
    rw [haction]
    exact hL
  · let J : Matrix (Fin 3) (Fin 3) ℝ := !![-1, 0, 0; 0, 1, 0; 0, 0, 1]
    have hJ : J ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
      rw [Matrix.mem_orthogonalGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [J, Matrix.mul_apply, Fin.sum_univ_succ]
    have hJdet : J.det = -1 := by simp [J, Matrix.det_fin_three]
    have hJu : Matrix.toEuclideanLin J u = u := by
      ext i
      fin_cases i <;>
        simp [J, u, axisUnit, EuclideanSpace.single]
    refine ⟨⟨M * J, Matrix.mem_specialOrthogonalGroup_iff.mpr
      ⟨(Matrix.orthogonalGroup (Fin 3) ℝ).mul_mem hM hJ, ?_⟩⟩, ?_⟩
    · rw [Matrix.det_mul, hn, hJdet]
      norm_num
    · change Matrix.toEuclideanLin (M * J) u = x
      rw [matrix_action_mul, hJu, haction]
      exact hL



theorem standardRotation_inner
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (x y : StandardCapSpace) :
    inner ℝ (standardRotation A x) (standardRotation A y) = inner ℝ x y := by
  have hA := (Matrix.mem_specialOrthogonalGroup_iff.mp A.property).1
  have hAA := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hA
  change (A.1 *ᵥ y.ofLp) ⬝ᵥ (A.1 *ᵥ x.ofLp) = y.ofLp ⬝ᵥ x.ofLp
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hAA, Matrix.vecMul_one]



theorem standardRotation_mul
    (A B : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (x : StandardCapSpace) :
    standardRotation (A * B) x = standardRotation A (standardRotation B x) :=
  matrix_action_mul A.1 B.1 x


theorem standardRotation_one (x : StandardCapSpace) : standardRotation 1 x = x := by
  change Matrix.toEuclideanLin (1 : Matrix (Fin 3) (Fin 3) ℝ) x = x
  simp


theorem standardRotation_inv_apply
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (x : StandardCapSpace) :
    standardRotation A (standardRotation A⁻¹ x) = x := by
  rw [← standardRotation_mul, mul_inv_cancel, standardRotation_one]

end PoincareConjecture.M35.Uniqueness
