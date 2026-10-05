import PoincareLib.Geometry.Riemannian.Comparison.Volume.Jacobi.Matrix

/-!
# Removing the radial direction from a Jacobi matrix

An adapted orthonormal basis puts the radial direction first. The principal
minor on the remaining basis vectors is the transverse matrix. Its determinant
removes the radial eigenvalue, and its trace retains the full curvature trace
when the radial direction lies in the kernel.

Reference: Morgan--Tian, Theorem 1.34, p. 19.
-/

noncomputable section
set_option autoImplicit false

open scoped BigOperators

namespace PoincareMT.RiemannianMetric

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A unit radial direction can be chosen as the first vector of an orthonormal basis. -/
theorem exists_orthonormalBasis_radial
    (θ : EuclideanSpace ℝ (Fin (m + 1))) (hθ : ‖θ‖ = 1) :
    ∃ b : OrthonormalBasis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))), b 0 = θ := by
  have ho : Orthonormal ℝ (({0} : Set (Fin (m + 1))).domRestrict (fun _ => θ)) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    exact hθ
  obtain ⟨b, hb⟩ := ho.exists_orthonormalBasis_extension_of_card_eq (by simp)
  exact ⟨b, hb 0 (by simp)⟩

/-- Removing a radial eigenvector factors its eigenvalue out of the determinant. -/
theorem det_eq_radial_mul_transverse
    (b : OrthonormalBasis (Fin (m + 1)) ℝ E) (A : E →L[ℝ] E) (t : ℝ)
    (hrad : A (b 0) = t • b 0) :
    (LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap).det =
      t * ((LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap).submatrix
        Fin.succ Fin.succ).det := by
  have hcol (i : Fin (m + 1)) :
      LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap i 0 =
        if i = 0 then t else 0 := by
    simp [LinearMap.toMatrix_apply, hrad]
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [hcol]

/-- A curvature operator annihilating the radial vector has the same trace
as its transverse matrix. -/
theorem trace_transverse_eq
    (b : OrthonormalBasis (Fin (m + 1)) ℝ E) (A : E →L[ℝ] E)
    (hrad : A (b 0) = 0) :
    ((LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap).submatrix
      Fin.succ Fin.succ).trace =
      (LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply, Fin.sum_univ_succ]
  simp [LinearMap.toMatrix_apply, hrad]

/-- Removing the radial direction preserves symmetry. -/
theorem isSymm_transverse
    (b : OrthonormalBasis (Fin (m + 1)) ℝ E) (A : E →L[ℝ] E)
    (hA : LinearMap.IsSymmetric A.toLinearMap) :
    ((LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap).submatrix
      Fin.succ Fin.succ).IsSymm := by
  have h := (LinearMap.isHermitian_toMatrix_iff b).mpr hA
  rw [Matrix.isHermitian_iff_isSymm] at h
  exact h.submatrix _

end PoincareMT.RiemannianMetric
