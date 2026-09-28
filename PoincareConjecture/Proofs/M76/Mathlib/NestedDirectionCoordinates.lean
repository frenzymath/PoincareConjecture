import PoincareConjecture.Proofs.M76.Mathlib.OrthogonalCylinderCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicConvexCoordinates









set_option autoImplicit false

open Set

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]




noncomputable def nestedDirectionCoordinates (L T : Submodule ℝ E) (hLT : L ≤ T) :
    (L × ↥((L.comap T.subtype)ᗮ)) ≃L[ℝ] T :=
  (((comapSubtypeEquivOfLe hLT).symm.toContinuousLinearEquiv.prodCongr
    (ContinuousLinearEquiv.refl ℝ ↥((L.comap T.subtype)ᗮ))).trans
      (ContinuousLinearEquiv.prodComm ℝ _ _)).trans
        (L.comap T.subtype).normalTangentEquiv.symm




theorem nestedDirectionCoordinates_apply_zero (L T : Submodule ℝ E) (hLT : L ≤ T)
    (x : L) : ((L.nestedDirectionCoordinates T hLT (x, 0) : T) : E) = x := by
  change ((0 : T) + ((comapSubtypeEquivOfLe hLT).symm x : T) : E) = x
  change (0 : E) + (x : E) = x
  exact zero_add _



noncomputable def affineSlice (T : Submodule ℝ E) (p : E) : T →ᴬ[ℝ] E :=
  ((AffineIsometryEquiv.vaddConst ℝ p).toAffineIsometry.comp
    T.subtypeₗᵢ.toAffineIsometry).toContinuousAffineMap

omit [FiniteDimensional ℝ E] in


theorem affineSlice_apply (T : Submodule ℝ E) (p : E) (x : T) :
    T.affineSlice p x = (x : E) + p := rfl

omit [FiniteDimensional ℝ E] in


theorem affineSlice_contLinear (T : Submodule ℝ E) (p : E) :
    (T.affineSlice p).contLinear = T.subtypeL := by
  ext x
  rfl




theorem affineSlice_nestedDirectionCoordinates (A : AffineSubspace ℝ E)
    (T : Submodule ℝ E) (hAT : A.direction ≤ T) (p : A) (x : A.direction) :
    T.affineSlice p (A.direction.nestedDirectionCoordinates T hAT (x, 0)) =
      A.directionCoordinates p x := by
  rw [affineSlice_apply, nestedDirectionCoordinates_apply_zero,
    AffineSubspace.directionCoordinates_apply]

end Submodule
