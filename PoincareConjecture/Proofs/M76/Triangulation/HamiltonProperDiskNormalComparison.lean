import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskConvexSigns










set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.HamiltonIndexOne

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem det_eq_tangent_mul_normal
    (a : (E × ℝ) →ₗ[ℝ] (E × ℝ)) (b : E →ₗ[ℝ] E)
    (hplane : ∀ x : E, a (x, 0) = (b x, 0)) :
    LinearMap.det a = LinearMap.det b * (a (0, 1)).2 := by
  classical
  let v := Module.finBasis ℝ E
  let r := Module.Basis.singleton Unit ℝ
  let c := v.prod r
  let U : Matrix (Fin (Module.finrank ℝ E)) Unit ℝ :=
    fun i _ => v.repr (a (0, 1)).1 i
  let D : Matrix Unit Unit ℝ := fun _ _ => (a (0, 1)).2
  have hm : LinearMap.toMatrix c c a =
      Matrix.fromBlocks (LinearMap.toMatrix v v b) U 0 D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [c, r, U, D, LinearMap.toMatrix_apply, Module.Basis.prod_apply, hplane,
        Matrix.fromBlocks]
  rw [← LinearMap.det_toMatrix c a, hm, Matrix.det_fromBlocks_zero₂₁,
    LinearMap.det_toMatrix]
  rw [Matrix.det_unique D]

omit [FiniteDimensional ℝ E] in
private def tangentNormalMap (P : E →ᵃ[ℝ] (E × ℝ)) (v : E × ℝ) :
    (E × ℝ) →ₗ[ℝ] (E × ℝ) :=
  P.linear.comp (LinearMap.fst ℝ E ℝ) + (LinearMap.snd ℝ E ℝ).smulRight v



noncomputable def affineDiskNormal (P : E →ᵃ[ℝ] (E × ℝ)) (w : E × ℝ) : ℝ :=
  LinearMap.det (tangentNormalMap P (w - P 0))





theorem affineDiskNormal_eq_of_plane_formula
    (P : E →ᵃ[ℝ] (E × ℝ)) (A : (E × ℝ) ≃ᵃ[ℝ] (E × ℝ)) (B : E ≃ᵃ[ℝ] E)
    (hplane : ∀ x : E, A (x, 0) = P (B x)) (w : E × ℝ) :
    affineDiskNormal P w = LinearMap.det (A.linear : (E × ℝ) →ₗ[ℝ] (E × ℝ)) *
      (LinearMap.det (B.linear.symm : E →ₗ[ℝ] E) * (A.symm w).2) := by
  have hcomp (x : E) : A.linear (x, 0) = P.linear (B.linear x) := by
    calc
      A.linear (x, 0) = A (x, 0) - A (0, 0) := by
        have h := A.map_vadd (0, 0) (x, 0)
        change A ((x, 0) + 0) = A.linear (x, 0) + A (0, 0) at h
        rw [add_zero] at h
        exact (sub_eq_of_eq_add h).symm
      _ = P (B x) - P (B 0) := by rw [hplane, hplane]
      _ = P.linear (B x - B 0) := (P.linearMap_vsub (B x) (B 0)).symm
      _ = P.linear (B.linear x) := by
        have h := B.map_vadd 0 x
        change B (x + 0) = B.linear x + B 0 at h
        rw [add_zero] at h
        exact congrArg P.linear (sub_eq_of_eq_add h)
  have hlinear (x : E) : P.linear x = A.linear (B.linear.symm x, 0) := by
    simpa only [B.linear.apply_symm_apply] using (hcomp (B.linear.symm x)).symm
  let p0 : E × ℝ := (B.symm 0, 0)
  have hp0 : P 0 = A p0 := by
    simpa only [p0, B.apply_symm_apply] using (hplane (B.symm 0)).symm
  let v := A.symm w - p0
  let j : E →ₗ[ℝ] (E × ℝ) :=
    (LinearMap.inl ℝ E ℝ).comp (B.linear.symm : E →ₗ[ℝ] E)
  let C : (E × ℝ) →ₗ[ℝ] (E × ℝ) :=
    j.comp (LinearMap.fst ℝ E ℝ) + (LinearMap.snd ℝ E ℝ).smulRight v
  have hv : A.linear v = w - P 0 := by
    calc
      A.linear v = w - A p0 := by
        have h := A.map_vadd p0 v
        change A (v + p0) = A.linear v + A p0 at h
        rw [show v + p0 = A.symm w by exact sub_add_cancel _ _,
          A.apply_symm_apply] at h
        exact (sub_eq_of_eq_add h).symm
      _ = w - P 0 := by rw [← hp0]
  have hCplane (x : E) : C (x, 0) = (B.linear.symm x, 0) := by
    simp [C, j]
  have hCnormal : (C (0, 1)).2 = (A.symm w).2 := by
    simp [C, j, v, p0]
  have hfactor : tangentNormalMap P (w - P 0) =
      (A.linear : (E × ℝ) →ₗ[ℝ] (E × ℝ)).comp C := by
    apply LinearMap.ext
    intro p
    change P.linear p.1 + p.2 • (w - P 0) =
      A.linear ((B.linear.symm p.1, 0) + p.2 • v)
    rw [map_add, map_smul, ← hlinear, hv]
  rw [affineDiskNormal, hfactor, LinearMap.det_comp,
    det_eq_tangent_mul_normal C (B.linear.symm : E →ₗ[ℝ] E) hCplane, hCnormal]



theorem affineDiskNormal_mul_tangent_det
    (P : E →ᵃ[ℝ] (E × ℝ)) (A : (E × ℝ) ≃ᵃ[ℝ] (E × ℝ)) (B : E ≃ᵃ[ℝ] E)
    (hplane : ∀ x : E, A (x, 0) = P (B x)) (p : E × ℝ) :
    affineDiskNormal P (A p) * LinearMap.det (B.linear : E →ₗ[ℝ] E) =
      LinearMap.det (A.linear : (E × ℝ) →ₗ[ℝ] (E × ℝ)) * p.2 := by
  rw [affineDiskNormal_eq_of_plane_formula P A B hplane, A.symm_apply_apply]
  calc
    _ = LinearMap.det (A.linear : (E × ℝ) →ₗ[ℝ] (E × ℝ)) *
        ((LinearMap.det (B.linear.symm : E →ₗ[ℝ] E) *
          LinearMap.det (B.linear : E →ₗ[ℝ] E)) * p.2) := by ring
    _ = _ := by rw [B.linear.det_symm_mul_det, one_mul]




theorem affineDiskNormal_mul_pos_of_piece_signs
    (P Q : E →ᵃ[ℝ] (E × ℝ))
    (A C : (E × ℝ) ≃ᵃ[ℝ] (E × ℝ)) (B D : E ≃ᵃ[ℝ] E)
    (hP : ∀ x : E, A (x, 0) = P (B x))
    (hQ : ∀ x : E, C (x, 0) = Q (D x))
    (hambient : 0 < LinearMap.det (A.linear : (E × ℝ) →ₗ[ℝ] (E × ℝ)) *
      LinearMap.det (C.linear : (E × ℝ) →ₗ[ℝ] (E × ℝ)))
    (htangent : 0 < LinearMap.det (B.linear : E →ₗ[ℝ] E) *
      LinearMap.det (D.linear : E →ₗ[ℝ] E))
    (p q : E × ℝ) (hside : 0 < p.2 * q.2) :
    0 < affineDiskNormal P (A p) * affineDiskNormal Q (C q) := by
  have h1 := affineDiskNormal_mul_tangent_det P A B hP p
  have h2 := affineDiskNormal_mul_tangent_det Q C D hQ q
  have he : (affineDiskNormal P (A p) * affineDiskNormal Q (C q)) *
      (LinearMap.det (B.linear : E →ₗ[ℝ] E) * LinearMap.det (D.linear : E →ₗ[ℝ] E)) =
      (LinearMap.det (A.linear : (E × ℝ) →ₗ[ℝ] (E × ℝ)) *
        LinearMap.det (C.linear : (E × ℝ) →ₗ[ℝ] (E × ℝ))) * (p.2 * q.2) := by
    calc
      _ = (affineDiskNormal P (A p) * LinearMap.det (B.linear : E →ₗ[ℝ] E)) *
          (affineDiskNormal Q (C q) * LinearMap.det (D.linear : E →ₗ[ℝ] E)) := by ring
      _ = _ := by rw [h1, h2]; ring
  have hpos : 0 < (affineDiskNormal P (A p) * affineDiskNormal Q (C q)) *
      (LinearMap.det (B.linear : E →ₗ[ℝ] E) * LinearMap.det (D.linear : E →ₗ[ℝ] E)) := by
    rw [he]
    exact mul_pos hambient hside
  exact (mul_pos_iff_of_pos_right htangent).mp hpos

end PoincareConjecture.M76.HamiltonIndexOne
