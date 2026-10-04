import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.OrthogonalCylinderCoordinates
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.IntrinsicConvexCoordinates

/-!
# A full frame adapted to a smaller affine direction

Orthogonal decomposition inside a containing direction space supplies
the extra slice parameters while retaining intrinsic cell coordinates.
See Cairns 1940, pp. 803--805 and M76 derivation 64.
-/

set_option autoImplicit false

open Set

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Split a containing direction space into a prescribed subspace
and its internal orthogonal complement. See Cairns pp. 803--805
and M76 derivation 64. -/
noncomputable def nestedDirectionCoordinates (L T : Submodule ℝ E) (hLT : L ≤ T) :
    (L × ↥((L.comap T.subtype)ᗮ)) ≃L[ℝ] T :=
  (((comapSubtypeEquivOfLe hLT).symm.toContinuousLinearEquiv.prodCongr
    (ContinuousLinearEquiv.refl ℝ ↥((L.comap T.subtype)ᗮ))).trans
      (ContinuousLinearEquiv.prodComm ℝ _ _)).trans
        (L.comap T.subtype).normalTangentEquiv.symm

/-- With the extra coordinates zero, the full frame is exactly
the included smaller direction. See Cairns pp. 803--805 and
M76 derivation 64. -/
theorem nestedDirectionCoordinates_apply_zero (L T : Submodule ℝ E) (hLT : L ≤ T)
    (x : L) : ((L.nestedDirectionCoordinates T hLT (x, 0) : T) : E) = x := by
  change ((0 : T) + ((comapSubtypeEquivOfLe hLT).symm x : T) : E) = x
  change (0 : E) + (x : E) = x
  exact zero_add _

/-- A full linear slice translated to a cell basepoint is a
continuous affine map. See Cairns pp. 803--805 and M76 derivation 64. -/
noncomputable def affineSlice (T : Submodule ℝ E) (p : E) : T →ᴬ[ℝ] E :=
  ((AffineIsometryEquiv.vaddConst ℝ p).toAffineIsometry.comp
    T.subtypeₗᵢ.toAffineIsometry).toContinuousAffineMap

omit [FiniteDimensional ℝ E] in
/-- The affine slice is translation of the included direction.
See Cairns pp. 803--805 and M76 derivation 64. -/
theorem affineSlice_apply (T : Submodule ℝ E) (p : E) (x : T) :
    T.affineSlice p x = (x : E) + p := rfl

omit [FiniteDimensional ℝ E] in
/-- The linear part of the full affine slice is the subtype map.
See Cairns pp. 803--805 and M76 derivation 64. -/
theorem affineSlice_contLinear (T : Submodule ℝ E) (p : E) :
    (T.affineSlice p).contLinear = T.subtypeL := by
  ext x
  rfl

/-- The zero-parameter full slice recovers the intrinsic affine
coordinates of the cell exactly. See Cairns pp. 803--805 and
M76 derivation 64. -/
theorem affineSlice_nestedDirectionCoordinates (A : AffineSubspace ℝ E)
    (T : Submodule ℝ E) (hAT : A.direction ≤ T) (p : A) (x : A.direction) :
    T.affineSlice p (A.direction.nestedDirectionCoordinates T hAT (x, 0)) =
      A.directionCoordinates p x := by
  rw [affineSlice_apply, nestedDirectionCoordinates_apply_zero,
    AffineSubspace.directionCoordinates_apply]

end Submodule
