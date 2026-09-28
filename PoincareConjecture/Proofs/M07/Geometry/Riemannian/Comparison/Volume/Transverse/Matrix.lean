import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Jacobi.Matrix

noncomputable section
set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.RiemannianMetric

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_orthonormalBasis_radial
    (θ : EuclideanSpace ℝ (Fin (m + 1))) (hθ : ‖θ‖ = 1) :
    ∃ b : OrthonormalBasis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))), b 0 = θ := by
  have ho : Orthonormal ℝ (({0} : Set (Fin (m + 1))).domRestrict (fun _ => θ)) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    exact hθ
  obtain ⟨b, hb⟩ := ho.exists_orthonormalBasis_extension_of_card_eq (by simp)
  exact ⟨b, hb 0 (by simp)⟩

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

theorem trace_transverse_eq
    (b : OrthonormalBasis (Fin (m + 1)) ℝ E) (A : E →L[ℝ] E)
    (hrad : A (b 0) = 0) :
    ((LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap).submatrix
      Fin.succ Fin.succ).trace =
      (LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply, Fin.sum_univ_succ]
  simp [LinearMap.toMatrix_apply, hrad]

theorem isSymm_transverse
    (b : OrthonormalBasis (Fin (m + 1)) ℝ E) (A : E →L[ℝ] E)
    (hA : LinearMap.IsSymmetric A.toLinearMap) :
    ((LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap).submatrix
      Fin.succ Fin.succ).IsSymm := by
  have h := (LinearMap.isHermitian_toMatrix_iff b).mpr hA
  rw [Matrix.isHermitian_iff_isSymm] at h
  exact h.submatrix _

end PoincareConjecture.RiemannianMetric
