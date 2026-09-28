import PoincareConjecture.Proofs.M76.Mathlib.FaceStarOperatorCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.CenteredSecantBounds
import PoincareConjecture.Proofs.M76.Mathlib.IndependentSecantBound
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional











set_option autoImplicit false

open Set ContinuousLinearMap AbstractSimplicialComplex
open scoped Pointwise

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [NormedAddCommGroup F] [NormedSpace ℝ F]




theorem exists_pos_secant_bound_frame_closedFaceStar (K : SimplicialComplex ℝ E)
    (hv : AffineIndependent ℝ ((↑) : K.vertices → E))
    {s : Finset E} (hs : s ∈ K.faces) {p : E}
    (hp : p ∈ affineSpan ℝ (s : Set E))
    (J : F →L[ℝ] ↥((affineSpan ℝ (s : Set E)).directionᗮ))
    (Q : FrameEmbeddingSpace ((affineSpan ℝ (s : Set E)).direction.frameWithTangent J)
      (K.closedFaceStar s).space) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ (K.closedFaceStar s).space,
      ∀ y ∈ (K.closedFaceStar s).space, c * ‖x - y‖ ≤ ‖Q.val x - Q.val y‖ := by
  let L := (affineSpan ℝ (s : Set E)).direction
  let S := (K.closedFaceStar s).space
  let N := L.normalAffineProjection p '' S
  let R : TangentCylinderEmbeddingSpace J N L := K.faceStarCylinderHomeomorph hs p J Q
  let blocks := tangentCylinderBlocks J N R
  have hform : R.val = tangentCylinderProjection blocks.1.val blocks.2.val :=
    R.val.eq_tangentCylinderProjection_of_fixed_tangent
      (fixed_tangent_of_rightInverse_productFrame J R.val R.property.1)
  have hlin := K.linearIndependent_faceLink_normal hv hs hp
  let : Finite (K.faceLink s).vertices :=
    finite_of_fin_dim_affineIndependent ℝ hlin.affineIndependent
  let v := K.faceNormalRadialEmbedding hv hs hp
  have hnormal : N = v.cone.space := K.normal_image_closedFaceStar hv hs hp
  have hinj : InjOn blocks.1.val v.cone.space := hnormal ▸ blocks.1.property.2
  obtain ⟨c, hc, hb⟩ :=
    v.exists_pos_secant_bound_of_linearIndependent hlin blocks.1.val hinj
  have hbN : ∀ x ∈ N, ∀ y ∈ N, c * ‖x - y‖ ≤ ‖blocks.1.val x - blocks.1.val y‖ := by
    rwa [← hnormal] at hb
  obtain ⟨d, hd, hdc⟩ := exists_pos_secant_bound_tangentCylinderProjection
    blocks.1.val blocks.2.val hc hbN
  have hsubset : (fun x => L.normalTangentEquiv (x - p)) '' S ⊆ N ×ˢ (univ : Set L) := by
    rw [show N ×ˢ (univ : Set L) =
      L.normalTangentCoordinates p '' (S + (L : Set E)) from
        (L.image_normalTangentCoordinates_add p S).symm]
    apply image_mono
    intro x hx
    exact ⟨x, hx, 0, L.zero_mem, add_zero x⟩
  apply L.normalTangentEquiv.exists_pos_secant_bound_of_centered_image Q.val p hd
  intro x hx y hy
  have h := hdc x (hsubset hx) y (hsubset hy)
  rw [← hform] at h
  exact h




theorem isSecantTransverse_ker_iff_injOn_frame_closedFaceStar
    (K : SimplicialComplex ℝ E) (hv : AffineIndependent ℝ ((↑) : K.vertices → E))
    {s : Finset E} (hs : s ∈ K.faces) {p : E}
    (hp : p ∈ affineSpan ℝ (s : Set E))
    (J : F →L[ℝ] ↥((affineSpan ℝ (s : Set E)).directionᗮ))
    (Q : E →L[ℝ] (F × (affineSpan ℝ (s : Set E)).direction))
    (hQ : Function.RightInverse ((affineSpan ℝ (s : Set E)).direction.frameWithTangent J) Q) :
    Q.ker.IsSecantTransverse (K.closedFaceStar s).space ↔
      InjOn Q (K.closedFaceStar s).space := by
  constructor
  · intro h
    exact h.injOn Q rfl
  · intro h
    obtain ⟨c, hc, hb⟩ := K.exists_pos_secant_bound_frame_closedFaceStar hv hs hp J ⟨Q, hQ, h⟩
    exact Submodule.isSecantTransverse_ker_of_lower_bound Q hc hb

end Geometry.SimplicialComplex
