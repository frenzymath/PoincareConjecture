import PoincareConjecture.Proofs.M76.Rigidity.OriginalProductRescaling

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1

noncomputable def periodLowerCoordinates (a : ℝ) : E →ᴬ[ℝ] E :=
  (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap.prod
    (a⁻¹ • (ContinuousLinearMap.snd ℝ V2 ℝ).toContinuousAffineMap)

noncomputable def periodUpperCoordinates (a p : ℝ) : E →ᴬ[ℝ] E :=
  (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap.prod
    (a⁻¹ • ((ContinuousLinearMap.snd ℝ V2 ℝ).toContinuousAffineMap -
      ContinuousAffineMap.const ℝ E p))

theorem periodLowerCoordinates_apply (a : ℝ) (z : E) :
    periodLowerCoordinates a z = (z.1, z.2 / a) := by
  change (z.1, a⁻¹ * z.2) = (z.1, z.2 / a)
  rw [div_eq_mul_inv, mul_comm]

theorem periodUpperCoordinates_apply (a p : ℝ) (z : E) :
    periodUpperCoordinates a p z = (z.1, (z.2 - p) / a) := by
  change (z.1, a⁻¹ * (z.2 - p)) = (z.1, (z.2 - p) / a)
  rw [div_eq_mul_inv, mul_comm]

theorem periodLowerCoordinates_mapsTo {a : ℝ} (ha : 0 < a) :
    MapsTo (periodLowerCoordinates a) (D ×ˢ Icc 0 (a / 2))
      (D ×ˢ Icc (0 : ℝ) (1 / 2)) := by
  intro z hz
  rw [periodLowerCoordinates_apply]
  refine ⟨hz.1, div_nonneg hz.2.1 ha.le, (div_le_iff₀ ha).mpr ?_⟩
  nlinarith [hz.2.2]

theorem periodUpperCoordinates_mapsTo {a p : ℝ} (ha : 0 < a) :
    MapsTo (periodUpperCoordinates a p) (D ×ˢ Icc (p - a / 2) p)
      (D ×ˢ Icc (-(1 / 2 : ℝ)) 0) := by
  intro z hz
  rw [periodUpperCoordinates_apply]
  refine ⟨hz.1, (le_div_iff₀ ha).mpr ?_, (div_le_iff₀ ha).mpr ?_⟩
  · nlinarith [hz.2.1]
  · linarith [hz.2.2]

theorem periodLowerCoordinates_mul {a : ℝ} (ha : a ≠ 0) (z : V2) (t : ℝ) :
    periodLowerCoordinates a (z, a * t) = (z, t) := by
  simp [periodLowerCoordinates_apply, ha]

theorem periodUpperCoordinates_add_mul {a : ℝ} (ha : a ≠ 0)
    (p : ℝ) (z : V2) (t : ℝ) :
    periodUpperCoordinates a p (z, p + a * t) = (z, t) := by
  simp [periodUpperCoordinates_apply, ha]

end PoincareConjecture.M76
