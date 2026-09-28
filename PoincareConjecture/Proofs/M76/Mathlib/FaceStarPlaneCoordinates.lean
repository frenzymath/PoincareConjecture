import PoincareConjecture.Proofs.M76.Mathlib.FaceStarSecantBound
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFaceTransversality
import PoincareConjecture.Proofs.M76.Mathlib.TransversePlaneDimension

set_option autoImplicit false

open Set ContinuousLinearMap

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def frameEmbeddingHomeomorph (J : F →L[ℝ] E) (S : Set E) :
    {Q : J.FrameProjectionSpace // InjOn Q.val S} ≃ₜ FrameEmbeddingSpace J S where
  toFun Q := ⟨Q.val.val, Q.val.property, Q.property⟩
  invFun Q := ⟨⟨Q.val, Q.property.1⟩, Q.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk (fun _ => _)
  continuous_invFun := continuous_subtype_val.subtype_mk (fun _ => _) |>.subtype_mk (fun _ => _)

end ContinuousLinearMap

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

noncomputable def faceStarComplementPlaneHomeomorph (K : SimplicialComplex ℝ E)
    (hv : AffineIndependent ℝ ((↑) : K.vertices → E))
    {s : Finset E} (hs : s ∈ K.faces) {p : E}
    (hp : p ∈ affineSpan ℝ (s : Set E))
    (J : F →L[ℝ] ↥((affineSpan ℝ (s : Set E)).directionᗮ))
    (hJ : Function.Injective J) :
    ((affineSpan ℝ (s : Set E)).direction.frameWithTangent J).range.TransverseComplementPlaneSpace
        (K.closedFaceStar s).space ≃ₜ
      FrameEmbeddingSpace ((affineSpan ℝ (s : Set E)).direction.frameWithTangent J)
        (K.closedFaceStar s).space := by
  let L := (affineSpan ℝ (s : Set E)).direction
  let J' := L.frameWithTangent J
  have hJ' : Function.Injective J' := L.injective_frameWithTangent hJ
  refine ((J'.frameComplementPlaneHomeomorph hJ').subtype ?_).trans
    (frameEmbeddingHomeomorph J' (K.closedFaceStar s).space)
  intro P
  rw [← K.isSecantTransverse_ker_iff_injOn_frame_closedFaceStar hv hs hp J
    ((J'.frameComplementPlaneHomeomorph hJ') P).val
      ((J'.frameComplementPlaneHomeomorph hJ') P).property,
    J'.ker_frameComplementPlaneHomeomorph hJ']

theorem contractible_faceStarComplementPlaneSpace (K : SimplicialComplex ℝ E)
    (hv : AffineIndependent ℝ ((↑) : K.vertices → E))
    {s : Finset E} (hs : s ∈ K.faces) {p : E}
    (hp : p ∈ affineSpan ℝ (s : Set E))
    (J : F →L[ℝ] ↥((affineSpan ℝ (s : Set E)).directionᗮ))
    (hJ : Function.Injective J)
    [ContractibleSpace (FrameEmbeddingSpace J
      ((affineSpan ℝ (s : Set E)).direction.normalAffineProjection p ''
        (K.closedFaceStar s).space))] :
    ContractibleSpace (Submodule.TransverseComplementPlaneSpace
      ((affineSpan ℝ (s : Set E)).direction.frameWithTangent J).range
      (K.closedFaceStar s).space) := by
  let := K.contractible_faceStarFrameEmbeddingSpace hs p J
  exact (K.faceStarComplementPlaneHomeomorph hv hs hp J hJ).contractibleSpace

theorem contractible_faceStarTransversePlaneSpace (K : SimplicialComplex ℝ E)
    (hv : AffineIndependent ℝ ((↑) : K.vertices → E))
    {s : Finset E} (hs : s ∈ K.faces) {p : E}
    (hp : p ∈ affineSpan ℝ (s : Set E))
    (J : F →L[ℝ] ↥((affineSpan ℝ (s : Set E)).directionᗮ))
    (hJ : Function.Injective J)
    {t : Finset E} (ht : t ∈ (K.closedFaceStar s).faces)
    (hframe : ((affineSpan ℝ (s : Set E)).direction.frameWithTangent J).range ≤
      (affineSpan ℝ (t : Set E)).direction)
    [ContractibleSpace (FrameEmbeddingSpace J
      ((affineSpan ℝ (s : Set E)).direction.normalAffineProjection p ''
        (K.closedFaceStar s).space))] :
    ContractibleSpace (SecantTransversePlaneSpace
      (Module.finrank ℝ F + Module.finrank ℝ (affineSpan ℝ (s : Set E)).direction)
      (K.closedFaceStar s).space) := by
  let L := (affineSpan ℝ (s : Set E)).direction
  let J' := L.frameWithTangent J
  have hdim : Module.finrank ℝ J'.range = Module.finrank ℝ F + Module.finrank ℝ L := by
    rw [LinearMap.finrank_range_of_inj (L.injective_frameWithTangent hJ), Module.finrank_prod]
  let := K.contractible_faceStarComplementPlaneSpace hv hs hp J hJ
  exact (transverseComplementHomeomorph _ (K.closedFaceStar s).space J'.range hdim
    (fun _ hP => ((K.closedFaceStar s).disjoint_faceDirection_of_isSecantTransverse ht hP).mono_left
      hframe)).contractibleSpace

end Geometry.SimplicialComplex
