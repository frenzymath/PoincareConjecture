import PoincareConjecture.Proofs.M76.Mathlib.NormalFaceStar
import PoincareConjecture.Proofs.M76.Mathlib.IndependentSecantBound










set_option autoImplicit false

open Set AbstractSimplicialComplex

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [NormedAddCommGroup F] [NormedSpace ℝ F]




theorem exists_pos_secant_bound_vertexStar (K : SimplicialComplex ℝ E)
    (hK : AffineIndependent ℝ ((↑) : K.vertices → E)) {p : E}
    (hp : {p} ∈ K.faces) (Q : E →L[ℝ] F)
    (hQ : InjOn Q (K.closedFaceStar {p}).space) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ (K.closedFaceStar {p}).space,
      ∀ y ∈ (K.closedFaceStar {p}).space, c * ‖x - y‖ ≤ ‖Q x - Q y‖ := by
  let L := (affineSpan ℝ (({p} : Finset E) : Set E)).direction
  have hL : L = ⊥ := by simp [L, direction_affineSpan]
  have hpA : p ∈ affineSpan ℝ (({p} : Finset E) : Set E) := by simp
  let a := L.normalAffineProjection p
  have ha (x : E) : (a x : E) = x - p := by
    change Lᗮ.starProjection (x - p) = x - p
    apply Submodule.starProjection_eq_self_iff.mpr
    simp [hL]
  let S := (K.closedFaceStar {p}).space
  let N := a '' S
  let R : ↥(Lᗮ) →L[ℝ] F := Q.comp Lᗮ.subtypeL
  have hlin := K.linearIndependent_faceLink_normal hK hp hpA
  let : Finite (K.faceLink {p}).vertices :=
    finite_of_fin_dim_affineIndependent ℝ hlin.affineIndependent
  let v := K.faceNormalRadialEmbedding hK hp hpA
  have hN : N = v.cone.space := K.normal_image_closedFaceStar hK hp hpA
  have hR : InjOn R N := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ he
    change Q (a x : E) = Q (a y : E) at he
    rw [ha, ha, map_sub, map_sub, sub_left_inj] at he
    exact congrArg a (hQ hx hy he)
  obtain ⟨c, hc, hb⟩ := v.exists_pos_secant_bound_of_linearIndependent hlin R (hN ▸ hR)
  refine ⟨c, hc, fun x hx y hy => ?_⟩
  have h := hb (a x) (hN ▸ mem_image_of_mem a hx) (a y) (hN ▸ mem_image_of_mem a hy)
  have hnorm : ‖a x - a y‖ = ‖x - y‖ := by
    change ‖(a x : E) - (a y : E)‖ = ‖x - y‖
    rw [ha, ha, sub_sub_sub_cancel_right]
  have hout : R (a x) - R (a y) = Q x - Q y := by
    change Q (a x : E) - Q (a y : E) = Q x - Q y
    rw [ha, ha, map_sub, map_sub, sub_sub_sub_cancel_right]
  rwa [hnorm, hout] at h

end Geometry.SimplicialComplex
