import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Boundary.Metric.RowFrame

/-! Signed reflection of the actual conformal boundary columns in
arbitrary dimension. This is the dimension-general row calculation
from M65 StrictTraceFrame, used for the true annular target.
Source: M65 derivation 43; M64 finite boundary collar derivation.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Complex
open scoped ContDiff

namespace PoincareMT.M64

open M65Branch

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Conjugation in the tangent row, negative conjugation in the others. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449; project derivations
`proof-work/tasks/M64/derivations/2026-09-26-finite-boundary-collar.md` and
`proof-work/tasks/M64/derivations/2026-09-26-periodic-finite-collar.md`. -/
def metricBoundaryReflection (j : Fin n) : (Fin n → ℂ) ≃ₗᵢ[ℝ] (Fin n → ℂ) := by
  let e (k : Fin n) : ℂ ≃ₗᵢ[ℝ] ℂ :=
    if k = j then conjLIE else conjLIE.trans (LinearIsometryEquiv.neg ℝ)
  exact {
    toLinearEquiv := LinearEquiv.piCongrRight fun k => (e k).toLinearEquiv
    norm_map' := fun v => by
      simp only [Pi.norm_def, LinearEquiv.piCongrRight_apply,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.nnnorm_map] }

/-- Coordinate formula for the signed conjugation. Source: Morgan--Tian (2007), Lemma 19.15,
pp. 447-449; project derivations
`proof-work/tasks/M64/derivations/2026-09-26-finite-boundary-collar.md` and
`proof-work/tasks/M64/derivations/2026-09-26-periodic-finite-collar.md`. -/
theorem metricBoundaryReflection_apply (j : Fin n) (v : Fin n → ℂ) (k : Fin n) :
    metricBoundaryReflection j v k = if k = j then star (v k) else -star (v k) := by
  simp only [metricBoundaryReflection, LinearIsometryEquiv.coe_mk,
    LinearEquiv.piCongrRight_apply]
  split_ifs <;> rfl

/-- The reflection is complex antilinear. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449; project derivations
`proof-work/tasks/M64/derivations/2026-09-26-finite-boundary-collar.md` and
`proof-work/tasks/M64/derivations/2026-09-26-periodic-finite-collar.md`. -/
theorem metricBoundaryReflection_smul (j : Fin n) (c : ℂ) (v : Fin n → ℂ) :
    metricBoundaryReflection j (c • v) = star c • metricBoundaryReflection j v := by
  ext k
  simp only [metricBoundaryReflection_apply, Pi.smul_apply, smul_eq_mul, star_mul]
  split_ifs <;> ring

/-- Reflecting twice gives the original vector. Source: Morgan--Tian (2007), Lemma 19.15,
pp. 447-449; project derivations
`proof-work/tasks/M64/derivations/2026-09-26-finite-boundary-collar.md` and
`proof-work/tasks/M64/derivations/2026-09-26-periodic-finite-collar.md`. -/
theorem metricBoundaryReflection_involutive (j : Fin n) :
    Function.Involutive (metricBoundaryReflection j) := by
  intro v
  ext k
  simp only [metricBoundaryReflection_apply]
  split_ifs <;> simp

/-- Conformality and the literal tangent direction separate the frame rows. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449; project derivations
`proof-work/tasks/M64/derivations/2026-09-26-finite-boundary-collar.md` and
`proof-work/tasks/M64/derivations/2026-09-26-periodic-finite-collar.md`. -/
theorem metricRowFrame_boundary_columns
    (G : E →L[ℝ] E →L[ℝ] ℝ) (V X Y : E) (j : Fin n) (hV : V j ≠ 0)
    (hpos : ∀ W : E, W ≠ 0 → 0 < G W W) (hX : ∃ a : ℝ, X = a • V)
    (hdiag : G X X = G Y Y) (hmixed : G X Y = 0) :
    metricRowFrame G V j Y j = 0 ∧ ∀ k, k ≠ j → metricRowFrame G V j X k = 0 := by
  obtain ⟨a, rfl⟩ := hX
  constructor
  · rw [metricRowFrame_apply, if_pos rfl]
    by_cases ha : a = 0
    · have hYY : G Y Y = 0 := by
        simpa only [ha, zero_smul, map_zero, zero_apply] using hdiag.symm
      have hY : Y = 0 := by
        by_contra hn
        exact (hpos Y hn).ne' hYY
      rw [hY, map_zero]
    · have hh : a * G V Y = 0 := by
        simpa only [map_smul, smul_apply, smul_eq_mul] using hmixed
      exact (mul_eq_zero.mp hh).resolve_left ha
  · intro k hk
    rw [metricRowFrame_apply, if_neg hk]
    simp only [PiLp.smul_apply, smul_eq_mul]
    field_simp
    ring

/-- Separated real and imaginary rows satisfy the reflection identity. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449; project derivations
`proof-work/tasks/M64/derivations/2026-09-26-finite-boundary-collar.md` and
`proof-work/tasks/M64/derivations/2026-09-26-periodic-finite-collar.md`. -/
theorem metricBoundaryReflection_of_rows (j : Fin n) (X Y : E)
    (hY : Y j = 0) (hX : ∀ k, k ≠ j → X k = 0) :
    metricBoundaryReflection j (coordinateComplexification X - I • coordinateComplexification Y) =
      coordinateComplexification X - I • coordinateComplexification Y := by
  ext k
  rw [metricBoundaryReflection_apply]
  change (if k = j then star ((X k : ℂ) - I * (Y k : ℂ)) else
    -star ((X k : ℂ) - I * (Y k : ℂ))) = (X k : ℂ) - I * (Y k : ℂ)
  by_cases hk : k = j
  · subst k
    simp [hY]
  · simp [hk, hX k hk]

/-- The actual framed conformal boundary differential is fixed by reflection. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449; project derivations
`proof-work/tasks/M64/derivations/2026-09-26-finite-boundary-collar.md` and
`proof-work/tasks/M64/derivations/2026-09-26-periodic-finite-collar.md`. -/
theorem metricRowFrame_boundary_reflection
    (G : E →L[ℝ] E →L[ℝ] ℝ) (V X Y : E) (j : Fin n) (hV : V j ≠ 0)
    (hpos : ∀ W : E, W ≠ 0 → 0 < G W W) (hX : ∃ a : ℝ, X = a • V)
    (hdiag : G X X = G Y Y) (hmixed : G X Y = 0) :
    metricBoundaryReflection j (complexifyOperator (metricRowFrame G V j)
      (coordinateComplexification X - I • coordinateComplexification Y)) =
      complexifyOperator (metricRowFrame G V j)
        (coordinateComplexification X - I • coordinateComplexification Y) := by
  obtain ⟨hY, hX⟩ := metricRowFrame_boundary_columns G V X Y j hV hpos hX hdiag hmixed
  simpa only [map_sub, map_smul, complexifyOperator_real] using
    metricBoundaryReflection_of_rows j (metricRowFrame G V j X) (metricRowFrame G V j Y) hY hX

end PoincareMT.M64
