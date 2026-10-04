import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.OriginalProductRescaling

/-!
# The two actual affine time changes in the full period cut

Both closed outer parameter pieces map into the same original
half-width product. Their exact inverse formulas retain the complete
disk parameter and every endpoint. See rigidity049, sections1--2.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1

/-- The actual lower-piece time rescaling. -/
noncomputable def periodLowerCoordinates (a : ℝ) : E →ᴬ[ℝ] E :=
  (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap.prod
    (a⁻¹ • (ContinuousLinearMap.snd ℝ V2 ℝ).toContinuousAffineMap)

/-- The actual upper-piece time shift and rescaling. -/
noncomputable def periodUpperCoordinates (a p : ℝ) : E →ᴬ[ℝ] E :=
  (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap.prod
    (a⁻¹ • ((ContinuousLinearMap.snd ℝ V2 ℝ).toContinuousAffineMap -
      ContinuousAffineMap.const ℝ E p))

/-- The lower time change fixes the complete disk parameter and divides time by a. -/
theorem periodLowerCoordinates_apply (a : ℝ) (z : E) :
    periodLowerCoordinates a z = (z.1, z.2 / a) := by
  change (z.1, a⁻¹ * z.2) = (z.1, z.2 / a)
  rw [div_eq_mul_inv, mul_comm]

/-- The upper time change fixes the disk parameter and rescales time relative to p. -/
theorem periodUpperCoordinates_apply (a p : ℝ) (z : E) :
    periodUpperCoordinates a p z = (z.1, (z.2 - p) / a) := by
  change (z.1, a⁻¹ * (z.2 - p)) = (z.1, (z.2 - p) / a)
  rw [div_eq_mul_inv, mul_comm]

/-- The entire lower piece lies in the nonnegative closed half
of the original product. See rigidity049, section1. -/
theorem periodLowerCoordinates_mapsTo {a : ℝ} (ha : 0 < a) :
    MapsTo (periodLowerCoordinates a) (D ×ˢ Icc 0 (a / 2))
      (D ×ˢ Icc (0 : ℝ) (1 / 2)) := by
  intro z hz
  rw [periodLowerCoordinates_apply]
  refine ⟨hz.1, div_nonneg hz.2.1 ha.le, (div_le_iff₀ ha).mpr ?_⟩
  nlinarith [hz.2.2]

/-- The entire upper piece lies in the nonpositive closed half
of the same original product. See rigidity049, section1. -/
theorem periodUpperCoordinates_mapsTo {a p : ℝ} (ha : 0 < a) :
    MapsTo (periodUpperCoordinates a p) (D ×ˢ Icc (p - a / 2) p)
      (D ×ˢ Icc (-(1 / 2 : ℝ)) 0) := by
  intro z hz
  rw [periodUpperCoordinates_apply]
  refine ⟨hz.1, (le_div_iff₀ ha).mpr ?_, (div_le_iff₀ ha).mpr ?_⟩
  · nlinarith [hz.2.1]
  · linarith [hz.2.2]

/-- Every original nonnegative time is recovered literally.
Its source interval bounds are handled by the caller. See049. -/
theorem periodLowerCoordinates_mul {a : ℝ} (ha : a ≠ 0) (z : V2) (t : ℝ) :
    periodLowerCoordinates a (z, a * t) = (z, t) := by
  simp [periodLowerCoordinates_apply, ha]

/-- Every original nonpositive time is recovered literally,
including the full upper period face. See rigidity049, section2. -/
theorem periodUpperCoordinates_add_mul {a : ℝ} (ha : a ≠ 0)
    (p : ℝ) (z : V2) (t : ℝ) :
    periodUpperCoordinates a p (z, p + a * t) = (z, t) := by
  simp [periodUpperCoordinates_apply, ha]

end PoincareMT.M76
