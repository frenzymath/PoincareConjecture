import PoincareConjecture.Proofs.M76.Mathlib.NormalFaceStar









set_option autoImplicit false

open Set
open scoped Pointwise

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]




noncomputable def normalTangentEquiv (L : Submodule ℝ E) : E ≃L[ℝ] (↥(Lᗮ) × L) where
  toFun x := (Lᗮ.orthogonalProjectionOnto x, L.orthogonalProjectionOnto x)
  invFun y := (y.1 : E) + (y.2 : E)
  left_inv x := by
    change Lᗮ.starProjection x + L.starProjection x = x
    rw [add_comm, L.starProjection_add_starProjection_orthogonal]
  right_inv y := by
    apply Prod.ext
    · change Lᗮ.orthogonalProjectionOnto ((y.1 : E) + (y.2 : E)) = y.1
      rw [map_add, Lᗮ.orthogonalProjectionOnto_mem_subspace_eq_self,
        L.orthogonalProjectionOnto_orthogonal_apply_eq_zero y.2.property, add_zero]
    · change L.orthogonalProjectionOnto ((y.1 : E) + (y.2 : E)) = y.2
      rw [map_add, L.orthogonalProjectionOnto_apply_of_mem_orthogonal y.1.property,
        L.orthogonalProjectionOnto_mem_subspace_eq_self, zero_add]
  map_add' x y := by ext <;> simp only [map_add, Prod.fst_add, Prod.snd_add]
  map_smul' c x := by ext <;> simp only [map_smul, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]
  continuous_toFun := Lᗮ.orthogonalProjectionOnto.continuous.prodMk
    L.orthogonalProjectionOnto.continuous
  continuous_invFun := (continuous_subtype_val.comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd)



theorem normalTangentEquiv_fst (L : Submodule ℝ E) (x : E) :
    (L.normalTangentEquiv x).1 = Lᗮ.orthogonalProjectionOnto x := rfl



theorem normalTangentEquiv_snd (L : Submodule ℝ E) (x : E) :
    (L.normalTangentEquiv x).2 = L.orthogonalProjectionOnto x := rfl



theorem normalTangentEquiv_symm_apply (L : Submodule ℝ E) (y : ↥(Lᗮ) × L) :
    L.normalTangentEquiv.symm y = (y.1 : E) + (y.2 : E) := rfl



noncomputable def normalTangentCoordinates (L : Submodule ℝ E) (p : E) :
    E ≃ₜ (↥(Lᗮ) × L) where
  toFun x := L.normalTangentEquiv (x - p)
  invFun y := L.normalTangentEquiv.symm y + p
  left_inv x := by
    dsimp only
    rw [ContinuousLinearEquiv.symm_apply_apply, sub_add_cancel]
  right_inv y := by
    dsimp only
    rw [add_sub_cancel_right, ContinuousLinearEquiv.apply_symm_apply]
  continuous_toFun := L.normalTangentEquiv.continuous.comp (continuous_id.sub continuous_const)
  continuous_invFun := L.normalTangentEquiv.symm.continuous.add continuous_const



theorem normalTangentCoordinates_apply (L : Submodule ℝ E) (p x : E) :
    L.normalTangentCoordinates p x = L.normalTangentEquiv (x - p) := rfl



theorem normalTangentCoordinates_fst (L : Submodule ℝ E) (p x : E) :
    (L.normalTangentCoordinates p x).1 = L.normalAffineProjection p x := rfl




theorem image_normalTangentCoordinates_add (L : Submodule ℝ E) (p : E) (S : Set E) :
    L.normalTangentCoordinates p '' (S + (L : Set E)) =
      (L.normalAffineProjection p '' S) ×ˢ (univ : Set L) := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, l, hl, rfl⟩, rfl⟩
    refine ⟨⟨x, hx, ?_⟩, mem_univ _⟩
    change Lᗮ.orthogonalProjectionOnto (x - p) =
      Lᗮ.orthogonalProjectionOnto ((x + l) - p)
    have he : (x + l) - p = (x - p) + l := by abel
    rw [he, map_add, L.orthogonalProjectionOnto_orthogonal_apply_eq_zero hl, add_zero]
  · rintro ⟨⟨x, hx, hn⟩, _⟩
    let l : L := y.2 - L.orthogonalProjectionOnto (x - p)
    refine ⟨x + (l : E), ⟨x, hx, l, l.property, rfl⟩, ?_⟩
    apply Prod.ext
    · change Lᗮ.orthogonalProjectionOnto ((x + (l : E)) - p) = y.1
      have he : (x + (l : E)) - p = (x - p) + l := by abel
      rw [he, map_add, L.orthogonalProjectionOnto_orthogonal_apply_eq_zero l.property, add_zero]
      exact hn
    · change L.orthogonalProjectionOnto ((x + (l : E)) - p) = y.2
      have he : (x + (l : E)) - p = (x - p) + l := by abel
      rw [he, map_add, L.orthogonalProjectionOnto_mem_subspace_eq_self]
      exact add_sub_cancel _ _

end Submodule
