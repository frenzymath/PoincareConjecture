import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.OrthogonalCylinderCoordinates
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.FaceStarInjectivity
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Products.TangentCylinderSpace

/-!
# Normalized operators on actual face stars

Centered orthogonal coordinates identify operators embedding a
closed face star with operators embedding its exact normal cylinder.
This transfers the normal-times-shear decomposition in actual
operator topology. See Cairns 1940, pp. 800--801, and M76 derivation 38.
-/

set_option autoImplicit false

open Set ContinuousLinearMap
open scoped Pointwise

namespace ContinuousLinearMap

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Changing linear coordinates and their center preserves
injectivity of an operator on the corresponding source set.
See Cairns p. 800 and M76 derivation 38. -/
theorem injOn_centered_image_iff (Q : E →L[ℝ] F) (e : E ≃L[ℝ] G) (p : E) (S : Set E) :
    InjOn (Q.comp e.symm.toContinuousLinearMap) ((fun x => e (x - p)) '' S) ↔
      InjOn Q S := by
  constructor
  · intro h x hx y hy he
    have he' : e (x - p) = e (y - p) := h (mem_image_of_mem _ hx)
      (mem_image_of_mem _ hy) (by
        simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.symm_apply_apply, map_sub] using
          congrArg (fun z => z - Q p) he)
    exact sub_left_inj.mp (e.injective he')
  · rintro h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ he
    have he' : Q x - Q p = Q y - Q p := by
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.symm_apply_apply, map_sub] using he
    rw [h hx hy (sub_left_inj.mp he')]

end ContinuousLinearMap

namespace Submodule

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Include a normal coordinate frame together with all tangent
directions into the actual ambient Euclidean space.
See Cairns pp. 800--801 and M76 derivation 38. -/
noncomputable def frameWithTangent (L : Submodule ℝ E) (J : F →L[ℝ] ↥(Lᗮ)) :
    (F × L) →L[ℝ] E :=
  L.normalTangentEquiv.symm.toContinuousLinearMap.comp
    (J.prodMap (ContinuousLinearMap.id ℝ L))

/-- An independent normal frame stays independent after adjoining
the tangent directions. See Cairns p. 800 and M76 derivation 38. -/
theorem injective_frameWithTangent (L : Submodule ℝ E) {J : F →L[ℝ] ↥(Lᗮ)}
    (hJ : Function.Injective J) : Function.Injective (L.frameWithTangent J) := by
  intro x y hxy
  have h := L.normalTangentEquiv.symm.injective hxy
  exact Prod.ext (hJ (congrArg (fun z : ↥(Lᗮ) × L => z.1) h))
    (congrArg (fun z : ↥(Lᗮ) × L => z.2) h)

end Submodule

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The normalized operator space of an actual nonempty face star
has exactly the coordinates of its full normal cylinder.
See Cairns Section 4, pp. 800--801, and M76 derivation 38. -/
noncomputable def faceStarCylinderHomeomorph (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) (p : E)
    (J : F →L[ℝ] ↥((affineSpan ℝ (s : Set E)).directionᗮ)) :
    FrameEmbeddingSpace ((affineSpan ℝ (s : Set E)).direction.frameWithTangent J)
        (K.closedFaceStar s).space ≃ₜ
      TangentCylinderEmbeddingSpace J
        ((affineSpan ℝ (s : Set E)).direction.normalAffineProjection p ''
          (K.closedFaceStar s).space) (affineSpan ℝ (s : Set E)).direction := by
  let L := (affineSpan ℝ (s : Set E)).direction
  let S := (K.closedFaceStar s).space
  refine (L.normalTangentEquiv.arrowCongr
    (ContinuousLinearEquiv.refl ℝ (F × L))).toHomeomorph.subtype ?_
  intro Q
  change (Function.RightInverse (L.frameWithTangent J) Q ∧ InjOn Q S) ↔
    (Function.RightInverse (J.prodMap (ContinuousLinearMap.id ℝ L))
      (Q.comp L.normalTangentEquiv.symm.toContinuousLinearMap) ∧
      InjOn (Q.comp L.normalTangentEquiv.symm.toContinuousLinearMap)
        ((L.normalAffineProjection p '' S) ×ˢ (univ : Set L)))
  apply and_congr Iff.rfl
  rw [← L.image_normalTangentCoordinates_add p S]
  exact ((Q.injOn_centered_image_iff L.normalTangentEquiv p (S + (L : Set E))).trans
    (K.injOn_closedFaceStar_tangent_iff hs Q.toLinearMap)).symm

/-- Contractibility of the actual normal embedding space transfers
to normalized operators on the original closed face star.
See Cairns pp. 800--801 and M76 derivation 38. -/
theorem contractible_faceStarFrameEmbeddingSpace (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) (p : E)
    (J : F →L[ℝ] ↥((affineSpan ℝ (s : Set E)).directionᗮ))
    [ContractibleSpace (FrameEmbeddingSpace J
      ((affineSpan ℝ (s : Set E)).direction.normalAffineProjection p ''
        (K.closedFaceStar s).space))] :
    ContractibleSpace (FrameEmbeddingSpace
      ((affineSpan ℝ (s : Set E)).direction.frameWithTangent J) (K.closedFaceStar s).space) := by
  let := contractible_tangentCylinderEmbeddingSpace J
    ((affineSpan ℝ (s : Set E)).direction.normalAffineProjection p '' (K.closedFaceStar s).space)
    (T := (affineSpan ℝ (s : Set E)).direction)
  exact (K.faceStarCylinderHomeomorph hs p J).contractibleSpace

end Geometry.SimplicialComplex
