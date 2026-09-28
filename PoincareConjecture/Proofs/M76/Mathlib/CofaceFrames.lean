import PoincareConjecture.Proofs.M76.Mathlib.FaceStarOperatorCoordinates










set_option autoImplicit false

namespace Submodule

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]




theorem frameWithTangent_range_le (L U : Submodule ℝ E) (J : F →L[ℝ] ↥(Lᗮ))
    (hL : L ≤ U) (hJ : ∀ z, (J z : E) ∈ U) : (L.frameWithTangent J).range ≤ U := by
  rintro x ⟨z, rfl⟩
  change (J z.1 : E) + (z.2 : E) ∈ U
  exact U.add_mem (hJ z.1) (hL z.2.property)

end Submodule

namespace AffineSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem normalAffineProjection_mem_direction (U V : AffineSubspace ℝ E)
    (hUV : U ≤ V) {p x : E} (hp : p ∈ U) (hx : x ∈ V) :
    (U.direction.normalAffineProjection p x : E) ∈ V.direction := by
  change U.directionᗮ.starProjection (x - p) ∈ V.direction
  rw [U.direction.starProjection_orthogonal_val]
  exact V.direction.sub_mem (V.vsub_mem_direction hx (hUV hp))
    (direction_le hUV (U.direction.starProjection_apply_mem (x - p)))




theorem normalLineFrame_range_le_direction (U V : AffineSubspace ℝ E)
    (hUV : U ≤ V) {p x : E} (hp : p ∈ U) (hx : x ∈ V) :
    (U.direction.frameWithTangent
      (ContinuousLinearMap.toSpanSingleton ℝ (U.direction.normalAffineProjection p x))).range ≤
      V.direction := by
  apply U.direction.frameWithTangent_range_le V.direction _ (direction_le hUV)
  intro r
  exact V.direction.smul_mem r (U.normalAffineProjection_mem_direction V hUV hp hx)

end AffineSubspace
