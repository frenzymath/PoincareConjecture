import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskChartSigns










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem affineDiskNormal_mul_ambient_det
    (P : E →ᵃ[ℝ] (E × ℝ)) (A : (E × ℝ) ≃ᵃ[ℝ] (E × ℝ)) (B : E ≃ᵃ[ℝ] E)
    (hplane : ∀ x : E, A (P x) = (B x, 0)) (w : E × ℝ) :
    affineDiskNormal P w * LinearMap.det (A.linear : (E × ℝ) →ₗ[ℝ] (E × ℝ)) =
      LinearMap.det (B.linear : E →ₗ[ℝ] E) * (A w).2 := by
  have hinverse (x : E) : A.symm (x, 0) = P (B.symm x) := by
    apply A.injective
    rw [A.apply_symm_apply, hplane, B.apply_symm_apply]
  have hnormal := affineDiskNormal_eq_of_plane_formula P A.symm B.symm hinverse w
  have hsymm : A.symm.symm w = A w := by
    apply A.symm.injective
    rw [A.symm.apply_symm_apply, A.symm_apply_apply]
  have hnormal' : affineDiskNormal P w =
      LinearMap.det (A.linear.symm : (E × ℝ) →ₗ[ℝ] (E × ℝ)) *
        (LinearMap.det (B.linear : E →ₗ[ℝ] E) * (A w).2) := by
    simpa only [AffineEquiv.linear_symm, LinearEquiv.symm_symm, hsymm] using hnormal
  calc
    _ = (LinearMap.det (A.linear.symm : (E × ℝ) →ₗ[ℝ] (E × ℝ)) *
        LinearMap.det (A.linear : (E × ℝ) →ₗ[ℝ] (E × ℝ))) *
        (LinearMap.det (B.linear : E →ₗ[ℝ] E) * (A w).2) := by rw [hnormal']; ring
    _ = _ := by rw [A.linear.det_symm_mul_det, one_mul]




theorem affineDiskNormal_mul_pos_of_forward_piece_signs
    (P Q : E →ᵃ[ℝ] (E × ℝ))
    (A C : (E × ℝ) ≃ᵃ[ℝ] (E × ℝ)) (B D : E ≃ᵃ[ℝ] E)
    (hP : ∀ x : E, A (P x) = (B x, 0))
    (hQ : ∀ x : E, C (Q x) = (D x, 0))
    (hambient : 0 < LinearMap.det (A.linear : (E × ℝ) →ₗ[ℝ] (E × ℝ)) *
      LinearMap.det (C.linear : (E × ℝ) →ₗ[ℝ] (E × ℝ)))
    (htangent : 0 < LinearMap.det (B.linear : E →ₗ[ℝ] E) *
      LinearMap.det (D.linear : E →ₗ[ℝ] E))
    (w z : E × ℝ) (hside : 0 < (A w).2 * (C z).2) :
    0 < affineDiskNormal P w * affineDiskNormal Q z := by
  have h1 := affineDiskNormal_mul_ambient_det P A B hP w
  have h2 := affineDiskNormal_mul_ambient_det Q C D hQ z
  have he : (affineDiskNormal P w * affineDiskNormal Q z) *
      (LinearMap.det (A.linear : (E × ℝ) →ₗ[ℝ] (E × ℝ)) *
        LinearMap.det (C.linear : (E × ℝ) →ₗ[ℝ] (E × ℝ))) =
      (LinearMap.det (B.linear : E →ₗ[ℝ] E) *
        LinearMap.det (D.linear : E →ₗ[ℝ] E)) * ((A w).2 * (C z).2) := by
    calc
      _ = (affineDiskNormal P w * LinearMap.det (A.linear : (E × ℝ) →ₗ[ℝ] (E × ℝ))) *
          (affineDiskNormal Q z * LinearMap.det (C.linear : (E × ℝ) →ₗ[ℝ] (E × ℝ))) := by ring
      _ = _ := by rw [h1, h2]; ring
  apply (mul_pos_iff_of_pos_right hambient).mp
  rw [he]
  exact mul_pos htangent hside

end PoincareConjecture.M76.HamiltonIndexOne
