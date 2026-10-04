import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Geometry
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The orbit of the first axis under the literal rotation action

Morgan-Tian Definition 12.1 and Lemma 12.3, pp. 293-295. A hyperplane
reflection carries vectors of equal length to one another. If needed,
precomposition by a fixed reflection preserving the first axis corrects
the determinant. The resulting actual special orthogonal matrix sends
the axis point of radius norm x to x, including x=0.
See the rotation-orbit derivation in the M34 task records.
-/

set_option autoImplicit false

open Matrix

namespace PoincareMT.M34

private def axisReflection : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, -1, 0; 0, 0, 1]

private theorem axisReflection_orthogonal :
    axisReflection ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [axisReflection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two]

private theorem axisReflection_det : axisReflection.det = -1 := by
  norm_num [axisReflection, Matrix.det_fin_three, Matrix.cons_val_two]

private theorem axisReflection_mulVec (r : ℝ) :
    axisReflection *ᵥ (EuclideanSpace.single (0 : Fin 3) r).ofLp =
      (EuclideanSpace.single (0 : Fin 3) r).ofLp := by
  ext i
  fin_cases i <;> simp [axisReflection, Matrix.mulVec, dotProduct]

/-- Every point lies in the actual SO(3) orbit of the nonnegative first
axis at its Euclidean radius (Lemma 12.3, pp. 294-295). -/
theorem exists_standardRotation_axis (x : StandardCapSpace) :
    ∃ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      standardRotation A (EuclideanSpace.single (0 : Fin 3) ‖x‖) = x := by
  let u : StandardCapSpace := EuclideanSpace.single 0 ‖x‖
  have hn : ‖u‖ = ‖x‖ := by simp [u]
  let T := (ℝ ∙ (u - x))ᗮ.reflection
  have hTx : T u = x := Submodule.reflection_sub hn
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let A := LinearMap.toMatrix b.toBasis b.toBasis T.toLinearMap
  have hA : A ∈ Matrix.orthogonalGroup (Fin 3) ℝ := T.toMatrix_mem_unitaryGroup b b
  have hAu : A *ᵥ u.ofLp = x.ofLp := by
    change A *ᵥ (b.toBasis.repr u) = b.toBasis.repr x
    rw [LinearMap.toMatrix_mulVec_repr]
    change (b.toBasis.repr (T u) : Fin 3 → ℝ) = b.toBasis.repr x
    rw [hTx]
  have hdet : A.det = 1 ∨ A.det = -1 := by
    have h := congrArg Matrix.det ((Matrix.mem_orthogonalGroup_iff _ _).mp hA)
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    apply sq_eq_one_iff.mp
    nlinarith
  rcases hdet with hp | hn
  · refine ⟨⟨A, Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨hA, hp⟩⟩, ?_⟩
    apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
    exact hAu
  · have hAR : A * axisReflection ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
      apply Matrix.mem_specialOrthogonalGroup_iff.mpr
      refine ⟨(Matrix.orthogonalGroup (Fin 3) ℝ).mul_mem hA axisReflection_orthogonal, ?_⟩
      rw [Matrix.det_mul, hn, axisReflection_det]
      norm_num
    refine ⟨⟨A * axisReflection, hAR⟩, ?_⟩
    apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
    change (A * axisReflection) *ᵥ u.ofLp = x.ofLp
    rw [← Matrix.mulVec_mulVec, axisReflection_mulVec]
    exact hAu

end PoincareMT.M34
